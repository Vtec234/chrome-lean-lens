#!/usr/bin/env python3
"""
Generate extension icons for Verso: Lean 4 GitHub Code Inspector.
Combines a modern gradient background with the Lean / Verso glyph (stylized V with lambda accent).
"""
import math
from PIL import Image, ImageDraw, ImageFont

def draw_icon(size):
    img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)

    # Rounded rectangle background
    pad = max(1, int(size * 0.06))
    radius = int(size * 0.22)
    
    # Gradient simulation or high-quality background
    # Verso / Lean palette: Deep slate violet to royal indigo
    # (#1e1e38 to #3b3a6e) with vibrant cyan/violet accents
    bg_color = (28, 32, 52, 255)       # Lean dark slate
    border_color = (88, 101, 242, 255) # Indigo border

    draw.rounded_rectangle(
        [pad, pad, size - pad - 1, size - pad - 1],
        radius=radius,
        fill=bg_color,
        outline=border_color,
        width=max(1, int(size * 0.04))
    )

    # Stylized "V" (for Verso) with Lean 4 accent (lambda / angle)
    # Coordinates normalized 0..1 mapped to size
    # Outer V
    v_left_x = int(size * 0.24)
    v_left_y = int(size * 0.26)
    v_mid_x = int(size * 0.50)
    v_mid_y = int(size * 0.76)
    v_right_x = int(size * 0.76)
    v_right_y = int(size * 0.26)
    line_w = max(2, int(size * 0.11))

    # Cyan / blue accent for the left arm
    cyan = (56, 189, 248, 255)
    # Violet / magenta accent for the right arm
    purple = (168, 85, 247, 255)

    # Draw left arm
    draw.line([(v_left_x, v_left_y), (v_mid_x, v_mid_y)], fill=cyan, width=line_w)
    # Draw right arm
    draw.line([(v_mid_x, v_mid_y), (v_right_x, v_right_y)], fill=purple, width=line_w)

    # Center dot / accent representing Lean proof state / target
    dot_r = max(1.5, size * 0.08)
    dot_cx = v_mid_x
    dot_cy = int(size * 0.38)
    draw.ellipse(
        [dot_cx - dot_r, dot_cy - dot_r, dot_cx + dot_r, dot_cy + dot_r],
        fill=(251, 191, 36, 255) # Warm amber/gold spark
    )

    return img

def main():
    sizes = [16, 32, 48, 128]
    for s in sizes:
        img = draw_icon(s)
        img.save(f"icons/icon{s}.png", "PNG")
        print(f"Generated icons/icon{s}.png")

    # Also generate an SVG version
    svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 128 128" width="128" height="128">
  <defs>
    <linearGradient id="bgGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#1f2438"/>
      <stop offset="100%" stop-color="#111422"/>
    </linearGradient>
    <linearGradient id="armLeft" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#38bdf8"/>
      <stop offset="100%" stop-color="#0284c7"/>
    </linearGradient>
    <linearGradient id="armRight" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#c084fc"/>
      <stop offset="100%" stop-color="#7c3aed"/>
    </linearGradient>
  </defs>
  <rect x="8" y="8" width="112" height="112" rx="26" fill="url(#bgGrad)" stroke="#6366f1" stroke-width="4"/>
  <path d="M 32 34 L 64 96" stroke="url(#armLeft)" stroke-width="14" stroke-linecap="round"/>
  <path d="M 64 96 L 96 34" stroke="url(#armRight)" stroke-width="14" stroke-linecap="round"/>
  <circle cx="64" cy="48" r="9" fill="#fbbf24"/>
</svg>"""
    with open("icons/icon.svg", "w") as f:
        f.write(svg)
    print("Generated icons/icon.svg")

if __name__ == "__main__":
    main()
