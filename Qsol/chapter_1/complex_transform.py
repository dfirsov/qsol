"""
Transform an image by multiplying every pixel coordinate by a complex number.

Each pixel at position (x, y) is treated as the complex number x + iy
(with the origin at the image center). After multiplication, the pixel
is placed at its new position in the output image.
"""

import re
import sys
import numpy as np
from PIL import Image


def parse_complex(s: str) -> complex:
    """Parse a complex number in the form 'a + ib' (or variants)."""
    s = s.strip().replace(" ", "")
    # Replace 'i' with 'j' for Python's complex literal syntax
    s = s.replace("i", "j")
    # 'j' alone (or '+j', '-j') means 1j / +1j / -1j
    s = re.sub(r"(?<![0-9\.])(j)", r"1\1", s)
    s = re.sub(r"([+-])(j)", r"\g<1>1\2", s)
    try:
        return complex(s)
    except ValueError:
        raise ValueError(f"Could not parse '{s}' as a complex number")


def transform_image(img: Image.Image, w: complex) -> Image.Image:
    """
    Return a new image where every source pixel at coordinate z = x+iy
    (centred at the image centre) is mapped to w*z.
    Uses inverse mapping + bilinear interpolation so there are no holes.
    """
    if abs(w) == 0:
        raise ValueError("Multiplying by zero collapses the image to a point.")

    # Convert image to a numpy array of shape (height, width, 3)
    src = np.array(img.convert("RGB"))
    # h = number of rows (vertical), width = number of columns (horizontal)
    h, width = src.shape[:2]
    # Centre of the image in pixel coordinates; used to shift the origin
    cx, cy = width / 2.0, h / 2.0

    # Express the four corners of the source image as complex numbers,
    # with the origin at the image centre rather than the top-left corner.
    # Top-left, top-right, bottom-left, bottom-right in centred coords:
    corners_z = [
        complex(-cx, -cy),           # top-left:     (0,     0    ) - centre
        complex(width - cx, -cy),    # top-right:    (width, 0    ) - centre
        complex(-cx, h - cy),        # bottom-left:  (0,     height) - centre
        complex(width - cx, h - cy), # bottom-right: (width, height) - centre
    ]
    # Multiply each corner by w to find where it lands in the output plane
    transformed = [w * z for z in corners_z]
    # The axis-aligned bounding box of the four transformed corners
    # tells us the minimum canvas size needed to contain the full output
    min_x = min(z.real for z in transformed)
    max_x = max(z.real for z in transformed)
    min_y = min(z.imag for z in transformed)
    max_y = max(z.imag for z in transformed)

    # Output canvas dimensions in pixels (add 1 to avoid off-by-one clipping)
    out_w = int(np.ceil(max_x - min_x)) + 1
    out_h = int(np.ceil(max_y - min_y)) + 1

    # The transformed corner with the smallest coordinates sits at output
    # pixel (0, 0); out_ox / out_oy are the offsets that achieve this shift
    out_ox = -min_x  # how far to shift the output origin horizontally
    out_oy = -min_y  # how far to shift the output origin vertically

    # Inverse of w: given an output coordinate z', the source coordinate is z = z' / w
    w_inv = 1.0 / w  # equivalent to conj(w) / |w|^2

    # Create a grid of every output pixel index: px = [0,1,...,out_w-1], etc.
    px = np.arange(out_w, dtype=np.float64)
    py = np.arange(out_h, dtype=np.float64)
    # xx[r,c] = c  (column index),  yy[r,c] = r  (row index) for every pixel
    xx, yy = np.meshgrid(px, py)  # both shape (out_h, out_w)

    # Shift output pixel indices so the origin is at the transformed centre,
    # matching the coordinate system used when we multiplied the corners
    xc = xx - out_ox
    yc = yy - out_oy

    # Apply the inverse transform (division by w = multiplication by w_inv)
    # to find, for each output pixel, which centred source coordinate it came from.
    # Complex multiplication (w_inv.real + i*w_inv.imag) * (xc + i*yc):
    #   real part: w_inv.real*xc - w_inv.imag*yc
    #   imag part: w_inv.imag*xc + w_inv.real*yc
    src_xc = w_inv.real * xc - w_inv.imag * yc  # centred source x
    src_yc = w_inv.imag * xc + w_inv.real * yc  # centred source y

    # Convert centred source coordinates back to pixel indices by re-adding the centre
    src_px = src_xc + cx  # source column (float)
    src_py = src_yc + cy  # source row    (float)

    # --- Bilinear interpolation ---
    # Each source coordinate is generally non-integer; we interpolate from the
    # four surrounding pixels (x0,y0), (x1,y0), (x0,y1), (x1,y1)
    x0 = np.floor(src_px).astype(np.int32)  # left neighbour column
    y0 = np.floor(src_py).astype(np.int32)  # top  neighbour row
    x1 = x0 + 1                              # right neighbour column
    y1 = y0 + 1                              # bottom neighbour row
    # Fractional distances from the top-left neighbour; extra axis for RGB broadcast
    dx = (src_px - x0)[..., np.newaxis]  # horizontal fraction in [0,1)
    dy = (src_py - y0)[..., np.newaxis]  # vertical   fraction in [0,1)

    # Mask: only output pixels whose source lands fully inside the source image
    valid = (x0 >= 0) & (x1 < width) & (y0 >= 0) & (y1 < h)

    # Clamp indices for the array lookup (out-of-bounds pixels are masked away by `valid`)
    x0c = np.clip(x0, 0, width - 1)
    x1c = np.clip(x1, 0, width - 1)
    y0c = np.clip(y0, 0, h - 1)
    y1c = np.clip(y1, 0, h - 1)

    # Weighted sum of the four neighbours; weights sum to 1
    interp = (
        src[y0c, x0c] * (1 - dx) * (1 - dy)  # top-left     weight: (1-dx)(1-dy)
        + src[y0c, x1c] * dx * (1 - dy)       # top-right    weight: dx(1-dy)
        + src[y1c, x0c] * (1 - dx) * dy       # bottom-left  weight: (1-dx)dy
        + src[y1c, x1c] * dx * dy             # bottom-right weight: dx*dy
    )

    # Black canvas; fill only the valid (in-bounds) pixels with interpolated colour
    out = np.zeros((out_h, out_w, 3), dtype=np.uint8)
    out[valid] = np.clip(interp[valid], 0, 255).astype(np.uint8)

    return Image.fromarray(out)


def main():
    raw = input("Enter complex number (e.g.  2 + 3i,  -1i,  0.5 + 0.5i): ")
    try:
        w = parse_complex(raw)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    path = input("Enter path to image: ").strip()
    try:
        img = Image.open(path)
    except FileNotFoundError:
        print(f"Error: file not found: {path}", file=sys.stderr)
        sys.exit(1)

    print(f"Transforming {img.size[0]}x{img.size[1]} image by w = {w} …")
    result = transform_image(img, w)
    result.save("out.jpg")
    print(f"Saved to out.jpg  ({result.size[0]}x{result.size[1]})")


if __name__ == "__main__":
    main()
