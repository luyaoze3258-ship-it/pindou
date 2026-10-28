// ============================================================================
// pindou-core.js - 照片转拼豆图纸（纯函数，浏览器 / Node / 微信 / 抖音小游戏通用）
//
// 算法与 devtools/pattern_gen.py 一致：去边框背景 → 裁主体 → 每格 4x4 采样众数映射色卡
// → 限色 → 去孤立点 → 按出现频率编号。输入是 RGBA 像素数组，不依赖 DOM。
//
// 图纸码格式（游戏端解码：scripts/Game/PatternCode.lua）：
//   PD1-<w>x<h>-<色卡>-<格子>-<校验>
//   色卡：每个局部色一个 base36 字符，值为全局色号（Palette.lua 下标，1..35）
//   格子：逐行展开后游程编码，'.' 空格，'A'..'Z' 局部色 1..26，后跟十进制次数（1 次省略）
//   校验：前面所有字符的字符码之和 mod 1296，2 位 base36
// ============================================================================
(function (root) {
  "use strict";

  const SAMPLES = 4;
  const B36 = "0123456789abcdefghijklmnopqrstuvwxyz";

  /** redmean 加权距离找最近色，返回全局色号（1 起） */
  function nearest(rgb, palette) {
    let best = 1, bestD = Infinity;
    for (let i = 0; i < palette.length; i++) {
      const p = palette[i];
      const rm = (rgb[0] + p[0]) / 2;
      const d = (2 + rm / 256) * (rgb[0] - p[0]) ** 2 + 4 * (rgb[1] - p[1]) ** 2 + (2 + (255 - rm) / 256) * (rgb[2] - p[2]) ** 2;
      if (d < bestD) { best = i + 1; bestD = d; }
    }
    return best;
  }

  /** 从四周泛洪，把和左上角背景色相近且连通的像素设为透明。已有透明像素时不处理。原地修改 data。 */
  function removeBorderBackground(data, w, h, tol = 40) {
    for (let i = 3; i < data.length; i += 4) if (data[i] < 128) return;
    const bg = [data[0], data[1], data[2]];
    const near = (i) => Math.abs(data[i] - bg[0]) + Math.abs(data[i + 1] - bg[1]) + Math.abs(data[i + 2] - bg[2]) <= tol;
    const seen = new Uint8Array(w * h);
    const stack = [];
    for (let x = 0; x < w; x++) stack.push(x, (h - 1) * w + x);
    for (let y = 0; y < h; y++) stack.push(y * w, y * w + w - 1);
    while (stack.length) {
      const p = stack.pop();
      if (seen[p] || !near(p * 4)) continue;
      seen[p] = 1;
      data[p * 4 + 3] = 0;
      const x = p % w, y = (p - x) / w;
      if (x + 1 < w) stack.push(p + 1);
      if (x > 0) stack.push(p - 1);
      if (y + 1 < h) stack.push(p + w);
      if (y > 0) stack.push(p - w);
    }
  }

  /** 不透明像素的包围盒 {x, y, w, h}，全透明返回 null */
  function opaqueBounds(data, w, h) {
    let x0 = w, y0 = h, x1 = -1, y1 = -1;
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        if (data[(y * w + x) * 4 + 3] >= 128) {
          if (x < x0) x0 = x;
          if (x > x1) x1 = x;
          if (y < y0) y0 = y;
          if (y > y1) y1 = y;
        }
      }
    }
    return x1 < 0 ? null : { x: x0, y: y0, w: x1 - x0 + 1, h: y1 - y0 + 1 };
  }

  /**
   * data 是已缩放到 (w*4) x (h*4) 的 RGBA 像素。返回 h 行 w 列的全局色号网格，0 = 空。
   * 每格取 16 个采样点映射色卡后的众数，硬边和细节不会被平均色糊掉。
   */
  function quantize(data, w, h, maxColors, palette) {
    const sw = w * SAMPLES;
    const cache = new Map();
    const grid = [];
    for (let y = 0; y < h; y++) {
      const row = [];
      for (let x = 0; x < w; x++) {
        const votes = new Map();
        for (let sy = 0; sy < SAMPLES; sy++) {
          for (let sx = 0; sx < SAMPLES; sx++) {
            const i = ((y * SAMPLES + sy) * sw + x * SAMPLES + sx) * 4;
            let c = 0;
            if (data[i + 3] >= 128) {
              const key = (data[i] << 16) | (data[i + 1] << 8) | data[i + 2];
              c = cache.get(key);
              if (c === undefined) { c = nearest([data[i], data[i + 1], data[i + 2]], palette); cache.set(key, c); }
            }
            votes.set(c, (votes.get(c) || 0) + 1);
          }
        }
        row.push(mostCommon(votes));
      }
      grid.push(row);
    }
    const used = new Map();
    for (const row of grid) for (const c of row) if (c) used.set(c, (used.get(c) || 0) + 1);
    const keep = rankByCount(used).slice(0, maxColors);
    const sub = keep.map((c) => palette[c - 1]);
    return grid.map((row) => row.map((c) => (c === 0 || keep.includes(c) ? c : keep[nearest(palette[c - 1], sub) - 1])));
  }

  /** 和上下左右（非空）邻居都不同的孤立格，改成邻居里最多的颜色 */
  function cleanIsolated(grid) {
    const h = grid.length, w = grid[0].length;
    const out = grid.map((r) => r.slice());
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const c = grid[y][x];
        if (!c) continue;
        const nb = [];
        for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
          const nx = x + dx, ny = y + dy;
          if (nx >= 0 && nx < w && ny >= 0 && ny < h && grid[ny][nx]) nb.push(grid[ny][nx]);
        }
        if (nb.length >= 2 && !nb.includes(c)) {
          const m = new Map();
          for (const n of nb) m.set(n, (m.get(n) || 0) + 1);
          out[y][x] = mostCommon(m);
        }
      }
    }
    return out;
  }

  /** 全局色号网格 -> { w, h, palette: [全局色号...按频率], cells: [局部色号...行优先, 0 = 空] } */
  function toPattern(grid) {
    const used = new Map();
    for (const row of grid) for (const c of row) if (c) used.set(c, (used.get(c) || 0) + 1);
    const order = rankByCount(used);
    const local = new Map(order.map((g, i) => [g, i + 1]));
    const cells = [];
    for (const row of grid) for (const c of row) cells.push(c ? local.get(c) : 0);
    return { w: grid[0].length, h: grid.length, palette: order, cells };
  }

  function checksum(s) {
    let n = 0;
    for (let i = 0; i < s.length; i++) n = (n + s.charCodeAt(i)) % 1296;
    return B36[Math.floor(n / 36)] + B36[n % 36];
  }

  function encode(p) {
    let rle = "";
    for (let i = 0; i < p.cells.length;) {
      let j = i;
      while (j < p.cells.length && p.cells[j] === p.cells[i]) j++;
      rle += (p.cells[i] === 0 ? "." : String.fromCharCode(64 + p.cells[i])) + (j - i > 1 ? String(j - i) : "");
      i = j;
    }
    const body = `PD1-${p.w}x${p.h}-${p.palette.map((g) => B36[g]).join("")}-${rle}`;
    return `${body}-${checksum(body)}`;
  }

  /**
   * 整条流水线：RGBA 原图 -> 图纸。
   * resize(data, w, h, crop, outW, outH) 由调用方提供（浏览器用 canvas，Node 测试用最近邻），返回缩放后的 RGBA。
   */
  function fromImage(data, w, h, opts, palette, resize) {
    const px = new Uint8ClampedArray(data);
    if (opts.removeBackground !== false) removeBorderBackground(px, w, h);
    const crop = opaqueBounds(px, w, h);
    if (!crop) return null;
    const gw = opts.size;
    const gh = Math.max(1, Math.round((gw * crop.h) / crop.w));
    const small = resize(px, w, h, crop, gw * SAMPLES, gh * SAMPLES);
    const grid = cleanIsolated(quantize(small, gw, gh, opts.colors, palette));
    return toPattern(grid);
  }

  function mostCommon(m) {
    let best = 0, bestN = -1;
    for (const [k, n] of m) if (n > bestN) { best = k; bestN = n; }
    return best;
  }

  function rankByCount(m) {
    return [...m.entries()].sort((a, b) => b[1] - a[1]).map((e) => e[0]);
  }

  const api = { SAMPLES, nearest, removeBorderBackground, opaqueBounds, quantize, cleanIsolated, toPattern, encode, checksum, fromImage };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.PindouCore = api;
})(typeof globalThis !== "undefined" ? globalThis : this);
