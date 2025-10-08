#!/usr/bin/env python3
"""
Generate various technical analysis chart patterns for blog post illustrations.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import matplotlib.patheffects as pe
import os

# Set style for consistent appearance
plt.style.use('seaborn-v0_8-darkgrid')

# Output directory (relative to this file, independent of CWD)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, '..', 'images'))

def generate_head_and_shoulders():
    """Generate a classic head and shoulders pattern with a clear neckline."""
    fig, ax = plt.subplots(figsize=(12, 6))

    # Construct deterministic H&S with three peaks (head highest) and two troughs (neckline)
    # Segment lengths sum to 200
    seg = {
        'pre': 30,
        'ls_up': 20,
        'ls_down': 20,
        'head_up': 20,
        'head_down': 20,
        'rs_up': 20,
        'rs_down': 20,
        'break': 50,
    }
    total = sum(seg.values())
    x = np.linspace(0, 100, total)

    # Levels
    base = 55.0
    ls_peak = 67.0
    head_peak = 74.0
    rs_peak = 66.0
    neck1 = 59.0
    neck2 = 58.0  # slanted neckline
    breakdown = 53.0

    # Build segments (piecewise linear)
    p = []
    # pre-uptrend
    p.append(np.linspace(base - 4, base, seg['pre']))
    # left shoulder up and down to neckline
    p.append(np.linspace(base, ls_peak, seg['ls_up']))
    p.append(np.linspace(ls_peak, neck1, seg['ls_down']))
    # head up and down to second neckline point
    p.append(np.linspace(neck1, head_peak, seg['head_up']))
    p.append(np.linspace(head_peak, neck2, seg['head_down']))
    # right shoulder up and down to neckline
    p.append(np.linspace(neck2, rs_peak, seg['rs_up']))
    p.append(np.linspace(rs_peak, (neck1 + neck2) / 2, seg['rs_down']))
    # breakdown
    p.append(np.linspace((neck1 + neck2) / 2, breakdown, seg['break']))
    p = np.concatenate(p)

    # Add enhanced small-scale movement (noise + gentle wiggle) for realism
    rng = np.random.default_rng(7)
    hf_wiggle = 0.4 * np.sin(np.linspace(0, 8 * np.pi, p.size))
    price = p + hf_wiggle + rng.normal(0, 0.5, size=p.shape)

    # Plot
    ax.plot(x, price, linewidth=2, color='#2E86AB', label='Price')

    # Neckline between the two troughs
    # Trough indices
    idx_neck1 = seg['pre'] + seg['ls_up'] + seg['ls_down'] - 1
    idx_neck2 = idx_neck1 + seg['head_up'] + seg['head_down']
    nx = np.array([x[idx_neck1], x[idx_neck2]])
    ny = np.array([neck1, neck2])
    ax.plot(nx, ny, '--', color='red', linewidth=2, label='Neckline', alpha=0.8)

    # Annotate peaks
    idx_ls_peak = seg['pre'] + seg['ls_up'] - 1
    idx_head_peak = idx_ls_peak + seg['ls_down'] + seg['head_up']
    idx_rs_peak = idx_head_peak + seg['head_down'] + seg['rs_up']
    ax.annotate('Left\nShoulder', xy=(x[idx_ls_peak], price[idx_ls_peak]),
                xytext=(x[idx_ls_peak], price[idx_ls_peak] + 5), ha='center',
                fontsize=11, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.5', facecolor='yellow', alpha=0.7))
    ax.annotate('Head', xy=(x[idx_head_peak], price[idx_head_peak]),
                xytext=(x[idx_head_peak], price[idx_head_peak] - 6), ha='center',
                fontsize=11, fontweight='bold',
                arrowprops=dict(arrowstyle='->', color='black', lw=1.5),
                bbox=dict(boxstyle='round,pad=0.5', facecolor='yellow', alpha=0.7))
    ax.annotate('Right\nShoulder', xy=(x[idx_rs_peak], price[idx_rs_peak]),
                xytext=(x[idx_rs_peak], price[idx_rs_peak] + 5), ha='center',
                fontsize=11, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.5', facecolor='yellow', alpha=0.7))

    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Price', fontsize=12)
    ax.set_title('Head and Shoulders Pattern', fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'head-shoulders-pattern.png'), dpi=300, bbox_inches='tight')
    print("Generated: head-shoulders-pattern.png")
    plt.close()


def generate_double_top_bottom():
    """Generate clean double top and double bottom patterns."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Shared x
    x = np.linspace(0, 100, 200)
    rng = np.random.default_rng(21)

    # ---- Double Top ----
    peak_level_1 = 68.0
    peak_level_2 = 69.0
    neckline = 60.0

    seg = [40, 20, 20, 40, 80]  # up to peak1, down to neck, up to peak2, break down, post
    p = []
    p.append(np.linspace(52, peak_level_1, seg[0]))
    p.append(np.linspace(peak_level_1, neckline, seg[1]))
    p.append(np.linspace(neckline, peak_level_2, seg[2]))
    p.append(np.linspace(peak_level_2, neckline - 3, seg[3]))  # breakdown
    p.append(np.linspace(neckline - 3, neckline - 1, seg[4]))
    p = np.concatenate(p)
    p = p + np.sin(np.linspace(0, 6*np.pi, p.size)) * 0.6
    # Add stronger stochastic jitter for realism
    p = p + rng.normal(0, 0.35, size=p.size)
    ax1.plot(x, p, linewidth=2, color='#2E86AB')
    # Resistance near tops
    ax1.axhline((peak_level_1 + peak_level_2) / 2, color='red', linestyle='--', linewidth=2, label='Resistance', alpha=0.8)
    # Annotations at approximate peak positions
    ax1.annotate('Peak 1', xy=(x[seg[0]-1], p[seg[0]-1]), xytext=(x[seg[0]-1], p[seg[0]-1] + 3),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.7))
    idx_peak2 = seg[0] + seg[1] + seg[2] - 1
    ax1.annotate('Peak 2', xy=(x[idx_peak2], p[idx_peak2]), xytext=(x[idx_peak2], p[idx_peak2] + 3),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.7))
    ax1.set_xlabel('Time', fontsize=11)
    ax1.set_ylabel('Price', fontsize=11)
    ax1.set_title('Double Top Pattern', fontsize=13, fontweight='bold')
    ax1.legend(loc='lower right')
    ax1.grid(True, alpha=0.3)

    # ---- Double Bottom ----
    trough_level_1 = 40.0
    trough_level_2 = 40.0
    neckline2 = 50.0
    segb = [40, 20, 20, 40, 80]  # down to trough1, up to neck, down to trough2, rally, post
    pb = []
    pb.append(np.linspace(58, trough_level_1, segb[0]))
    pb.append(np.linspace(trough_level_1, neckline2, segb[1]))
    pb.append(np.linspace(neckline2, trough_level_2, segb[2]))
    pb.append(np.linspace(trough_level_2, neckline2 + 5, segb[3]))  # breakout above neckline
    pb.append(np.linspace(neckline2 + 5, neckline2 + 3, segb[4]))
    pb = np.concatenate(pb)
    pb = pb + np.sin(np.linspace(0, 6*np.pi, pb.size)) * 0.6
    # Add stronger stochastic jitter for realism
    pb = pb + rng.normal(0, 0.35, size=pb.size)
    ax2.plot(x, pb, linewidth=2, color='#2E86AB')
    # Support near troughs
    ax2.axhline((trough_level_1 + trough_level_2) / 2, color='green', linestyle='--', linewidth=2, label='Support', alpha=0.8)
    # Annotations at troughs
    ax2.annotate('Bottom 1', xy=(x[segb[0]-1], pb[segb[0]-1]), xytext=(x[segb[0]-1], pb[segb[0]-1] - 3),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.7))
    idx_trough2 = segb[0] + segb[1] + segb[2] - 1
    ax2.annotate('Bottom 2', xy=(x[idx_trough2], pb[idx_trough2]), xytext=(x[idx_trough2], pb[idx_trough2] - 3),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.7))
    ax2.set_xlabel('Time', fontsize=11)
    ax2.set_ylabel('Price', fontsize=11)
    ax2.set_title('Double Bottom Pattern', fontsize=13, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'double-top-bottom-patterns.png'), dpi=300, bbox_inches='tight')
    print("Generated: double-top-bottom-patterns.png")
    plt.close()


def generate_support_resistance():
    """Generate support and resistance with exactly three top and three bottom touches.

    The price jitters up and down within the channel, but only touches the
    resistance and support lines three times each for a more realistic look.
    """
    fig, ax = plt.subplots(figsize=(12, 6))

    upper = 65.0
    lower = 45.0
    n = 300
    x = np.linspace(0, 100, n)

    rng = np.random.default_rng(42)
    eps = 0.2  # margin to avoid unintended extra touches

    def noisy_walk_segment(start, target, length, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0):
        """Create a jittery segment from start to target using cup/handle-like jitter.

        Matches the cup-and-handle jitter style: linear trend plus Gaussian
        noise with stdev≈0.5. Optionally a tiny sinusoid can be added via
        wiggle_scale, but defaults to 0 to mirror the cup’s look.
        """
        if length <= 1:
            return np.array([target], dtype=float)
        base = np.linspace(start, target, length)
        gauss_noise = rng.normal(0, noise_scale, size=length)
        wiggle = wiggle_scale * np.sin(np.linspace(0, 6*np.pi, length) + rng.uniform(0, 2*np.pi))
        seg = base + gauss_noise + wiggle
        if inside_clip:
            seg[1:-1] = np.clip(seg[1:-1], lower + eps, upper - eps)
        seg[-1] = target
        return seg

    # Allocate lengths (sum <= n)
    pre_len = 40
    L1 = 30
    L2 = 40
    L3 = 35
    L4 = 35
    L5 = 30
    L6 = 35
    post_len = n - (pre_len + L1 + L2 + L3 + L4 + L5 + L6)
    if post_len < 10:
        post_len = 10
        n2 = pre_len + L1 + L2 + L3 + L4 + L5 + L6 + post_len
        x = np.linspace(0, 100, n2)

    # Build path with exactly three hits at top and bottom
    path = []
    bounces = []

    current = 55.0
    # Pre wander inside channel without touching boundaries
    pre_noise = noisy_walk_segment(current, current, pre_len, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    current = float(pre_noise[-1])
    path.append(pre_noise)

    # 1: up to top
    seg1 = noisy_walk_segment(current, upper, L1, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg1)
    # record bounce index after concatenation later
    # 2: down to bottom
    seg2 = noisy_walk_segment(upper - 0.1, lower, L2, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg2)
    # 3: up to top
    seg3 = noisy_walk_segment(lower + 0.1, upper, L3, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg3)
    # 4: down to bottom
    seg4 = noisy_walk_segment(upper - 0.1, lower, L4, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg4)
    # 5: up to top
    seg5 = noisy_walk_segment(lower + 0.1, upper, L5, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg5)
    # 6: down to bottom
    seg6 = noisy_walk_segment(upper - 0.1, lower, L6, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(seg6)

    # Post wander without touching boundaries
    post_noise = noisy_walk_segment(lower + 5.0, lower + 7.5, post_len, inside_clip=True, noise_scale=0.5, wiggle_scale=0.0)
    path.append(post_noise)

    price = np.concatenate(path)

    # Compute bounce indices and types: ends of seg1..seg6 relative to full array
    lens = [len(pre_noise), len(seg1), len(seg2), len(seg3), len(seg4), len(seg5), len(seg6)]
    offsets = np.cumsum([0] + lens)
    # seg1 end
    bounces.append((offsets[1]-1, 'res'))
    # seg2 end
    bounces.append((offsets[2]-1, 'sup'))
    # seg3 end
    bounces.append((offsets[3]-1, 'res'))
    # seg4 end
    bounces.append((offsets[4]-1, 'sup'))
    # seg5 end
    bounces.append((offsets[5]-1, 'res'))
    # seg6 end
    bounces.append((offsets[6]-1, 'sup'))

    ax.plot(x, price, linewidth=2, color='#2E86AB', label='Price', alpha=0.9)

    # Draw support and resistance lines
    ax.axhline(y=upper, color='red', linestyle='--', linewidth=2.5, label='Resistance', alpha=0.7)
    ax.axhline(y=lower, color='green', linestyle='--', linewidth=2.5, label='Support', alpha=0.7)

    # Mark all six bounce points with short arrows (three top, three bottom)
    for (i, kind) in bounces:
        if i < len(x):
            if kind == 'res':
                ax.annotate('', xy=(x[i], price[i]), xytext=(x[i], price[i] + 3),
                            arrowprops=dict(arrowstyle='->', color='red', lw=2))
            else:
                ax.annotate('', xy=(x[i], price[i]), xytext=(x[i], price[i] - 3),
                            arrowprops=dict(arrowstyle='->', color='green', lw=2))

    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Price', fontsize=12)
    ax.set_title('Support and Resistance Levels', fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=11)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(40, 70)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'support-resistance.png'), dpi=300, bbox_inches='tight')
    print("Generated: support-resistance.png")
    plt.close()


def generate_cup_and_handle():
    """Generate a proper cup-and-handle pattern with U-shaped base and breakout."""
    fig, ax = plt.subplots(figsize=(12, 6))

    x = np.linspace(0, 100, 300)

    rim = 60.0
    depth = 15.0
    mid = 40.0
    scale = 30.0

    cup = np.full_like(x, rim, dtype=float)
    # U-shaped cup between (mid-scale) and (mid+scale)
    mask = (x >= (mid - scale)) & (x <= (mid + scale))
    cup_shape = rim - depth * (1 - ((x[mask] - mid) / scale) ** 2)
    cup[mask] = cup_shape

    # Handle: slight downward-sloping consolidation after the right rim
    handle_mask = x > 80
    handle_x = x[handle_mask]
    handle_len = handle_x[-1] - handle_x[0]
    handle_drop = 2.0
    handle = rim - (handle_drop * (handle_x - handle_x[0]) / max(handle_len, 1))
    handle += np.sin((handle_x - handle_x[0]) * 0.6) * 0.4
    cup[handle_mask] = handle

    # Breakout after handle
    bo_mask = x > 95
    cup[bo_mask] = rim + (x[bo_mask] - 95) * 0.8

    rng = np.random.default_rng(11)
    price = cup + rng.normal(0, 0.5, len(x))

    ax.plot(x, price, linewidth=2, color='#2E86AB', label='Price')
    ax.axhline(y=rim, color='red', linestyle='--', linewidth=2, label='Breakout Level', alpha=0.7)

    # Annotate parts
    ax.annotate('Cup', xy=(mid, rim - depth + 1), xytext=(mid, rim - depth - 4),
                ha='center', fontsize=12, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.5', facecolor='yellow', alpha=0.7))
    ax.annotate('Handle', xy=(88, rim - 1.0), xytext=(88, rim - 5.0),
                ha='center', fontsize=12, fontweight='bold',
                bbox=dict(boxstyle='round,pad=0.5', facecolor='lightblue', alpha=0.7))
    ax.annotate('Breakout', xy=(97, rim + 2.0), xytext=(97, rim + 7.0),
                ha='center', fontsize=11, fontweight='bold',
                arrowprops=dict(arrowstyle='->', color='green', lw=2),
                bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.7))

    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Price', fontsize=12)
    ax.set_title('Cup and Handle Pattern', fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=11)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'cup-handle-pattern.png'), dpi=300, bbox_inches='tight')
    print("Generated: cup-handle-pattern.png")
    plt.close()


def generate_flag_pennant():
    """Generate flag and pennant continuation patterns (clean structures)."""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    x = np.linspace(0, 100, 200)
    rng = np.random.default_rng(31)

    # ---- Flag ----
    # Pole
    pole_len = 80
    pole = np.linspace(40, 80, pole_len)
    # Flag (downward sloping parallel channel)
    flag_len = 50
    flag_x = np.linspace(0, 1, flag_len)
    upper = np.linspace(80, 74, flag_len)
    lower = np.linspace(76, 70, flag_len)
    mid = (upper + lower) / 2
    wiggle = np.sin(np.linspace(0, 3*np.pi, flag_len)) * (upper - lower) / 4
    flag = mid + wiggle
    # Breakout continuation
    bo_len = len(x) - (pole_len + flag_len)
    breakout = np.linspace(flag[-1], flag[-1] + 18, bo_len)
    # Add small-scale jitter: keep within/near channel during flag
    jitter_pole = rng.normal(0, 0.55, size=pole_len)
    width_flag = (upper - lower)
    jitter_flag = rng.normal(0, 0.18, size=flag_len) * width_flag
    jitter_breakout = rng.normal(0, 0.45, size=bo_len)
    price_flag = np.concatenate([pole + jitter_pole,
                                 flag + jitter_flag,
                                 breakout + jitter_breakout])

    ax1.plot(x, price_flag, linewidth=2, color='#2E86AB')
    # Channel boundaries
    x_flag = x[pole_len:pole_len+flag_len]
    ax1.plot([x_flag[0], x_flag[-1]], [upper[0], upper[-1]], 'r--', linewidth=1.8, alpha=0.8)
    ax1.plot([x_flag[0], x_flag[-1]], [lower[0], lower[-1]], 'r--', linewidth=1.8, alpha=0.8)
    ax1.annotate('Flagpole', xy=(x[pole_len//2], pole[pole_len//2]), xytext=(x[pole_len//2]-15, pole[pole_len//2]+7),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.7))
    ax1.annotate('Flag', xy=(x_flag[len(x_flag)//2], flag[len(flag)//2]), xytext=(x_flag[len(x_flag)//2], flag[len(flag)//2]-8),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightblue', alpha=0.7))
    ax1.annotate('Breakout', xy=(x[pole_len+flag_len+10], price_flag[pole_len+flag_len+10]),
                 xytext=(x[pole_len+flag_len+10], price_flag[pole_len+flag_len+10]-7),
                 ha='center', fontsize=10, fontweight='bold',
                 arrowprops=dict(arrowstyle='->', color='green', lw=2),
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.7))
    ax1.set_xlabel('Time', fontsize=11)
    ax1.set_ylabel('Price', fontsize=11)
    ax1.set_title('Flag Pattern', fontsize=13, fontweight='bold')
    ax1.grid(True, alpha=0.3)

    # ---- Pennant ----
    # Flagpole preceding pennant
    pole2 = pole.copy()
    # Converging triangle (pennant) that breaks out BEFORE the apex
    penn_len = 48
    p_upper = np.linspace(80, 78, penn_len)  # slopes down
    p_lower = np.linspace(76, 78, penn_len)  # slopes up
    p_mid = (p_upper + p_lower) / 2
    p_wiggle = np.sin(np.linspace(0, 3.2*np.pi, penn_len)) * (p_upper - p_lower) / 4
    pennant = p_mid + p_wiggle

    # Choose breakout to occur ~75% into the pennant (before apex)
    break_rel_idx = int(0.75 * penn_len)
    break_abs_idx = pole_len + break_rel_idx
    # Price path: pole -> pennant up to break -> breakout continuation
    pre_break = pennant[:break_rel_idx + 1]
    bo2_len = len(x) - (pole_len + break_rel_idx + 1)
    breakout_start = pre_break[-1]
    breakout2 = np.linspace(breakout_start, breakout_start + 20, bo2_len)
    # Add small-scale jitter in pennant: scale by narrowing width to stay reasonable
    width_penn = (p_upper[:break_rel_idx+1] - p_lower[:break_rel_idx+1])
    jitter_pole2 = rng.normal(0, 0.55, size=pole_len)
    jitter_penn = rng.normal(0, 0.18, size=pre_break.size) * width_penn
    # Optionally clip within boundaries with a small margin
    margin = 0.08 * width_penn
    pre_break_j = np.clip(pre_break + jitter_penn,
                          p_lower[:break_rel_idx+1] + margin,
                          p_upper[:break_rel_idx+1] - margin)
    jitter_breakout2 = rng.normal(0, 0.45, size=bo2_len)
    price_pennant = np.concatenate([pole2 + jitter_pole2,
                                    pre_break_j,
                                    breakout2 + jitter_breakout2])

    ax2.plot(x, price_pennant, linewidth=2, color='#2E86AB')
    # Draw pennant boundaries only up to breakout point
    x_penn = x[pole_len:pole_len + break_rel_idx + 1]
    ax2.plot([x_penn[0], x_penn[-1]], [p_upper[0], p_upper[break_rel_idx]], 'r--', linewidth=1.8, alpha=0.8)
    ax2.plot([x_penn[0], x_penn[-1]], [p_lower[0], p_lower[break_rel_idx]], 'r--', linewidth=1.8, alpha=0.8)
    ax2.annotate('Flagpole', xy=(x[pole_len//2], pole2[pole_len//2]), xytext=(x[pole_len//2]-15, pole2[pole_len//2]+7),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.7))
    ax2.annotate('Pennant', xy=(x_penn[len(x_penn)//2], pre_break[len(pre_break)//2]), xytext=(x_penn[len(x_penn)//2], pre_break[len(pre_break)//2]-8),
                 ha='center', fontsize=10, fontweight='bold',
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightblue', alpha=0.7))
    ax2.annotate('Breakout', xy=(x[break_abs_idx + 6], price_pennant[break_abs_idx + 6]),
                 xytext=(x[break_abs_idx + 6], price_pennant[break_abs_idx + 6]-7),
                 ha='center', fontsize=10, fontweight='bold',
                 arrowprops=dict(arrowstyle='->', color='green', lw=2),
                 bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.7))
    ax2.set_xlabel('Time', fontsize=11)
    ax2.set_ylabel('Price', fontsize=11)
    ax2.set_title('Pennant Pattern', fontsize=13, fontweight='bold')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'flag-pennant-patterns.png'), dpi=300, bbox_inches='tight')
    print("Generated: flag-pennant-patterns.png")
    plt.close()


def generate_moving_averages():
    """Generate moving average crossover chart (50 vs 200) with trailing MAs.

    Per request, the 200-day moving average starts at the beginning of the
    chart. We use trailing (no lookahead) moving averages with expanding
    windows at the start (i.e., min_periods = 1), so both the 50-day and
    200-day series begin at time 0 and extend to the end.
    """
    fig, ax = plt.subplots(figsize=(12, 6))

    np.random.seed(123)
    x = np.linspace(0, 200, 400)

    # Construct a piecewise price path to place crosses clearly:
    # - Early mild rise (0–10)
    # - Decline (10–35) to set up an early death cross (~30–35)
    # - Strong rise (35–70) to set up a golden cross (~70)
    # - Continued rise (70–200)
    y = np.empty_like(x)
    # 0–10: 50 -> 49 (slight early dip to avoid premature golden cross)
    m1 = x <= 10
    y[m1] = 50 + (x[m1] / 10.0) * (49 - 50)
    # 10–35: 49 -> 45
    m2 = (x > 10) & (x <= 35)
    y[m2] = 49 + ((x[m2] - 10) / 25.0) * (45 - 49)
    # 35–70: 45 -> 60
    m3 = (x > 35) & (x <= 70)
    y[m3] = 45 + ((x[m3] - 35) / 35.0) * (60 - 45)
    # 70–200: 60 -> 72
    m4 = x > 70
    y[m4] = 60 + ((x[m4] - 70) / 130.0) * (72 - 60)
    # Add modest noise/jitter without overwhelming the intended trend
    price = y + 0.8 * np.sin(x * 0.14) + np.random.normal(0, 1.0, len(x))

    # Helper: trailing moving average with expanding start (min_periods=1)
    def trailing_ma(arr, window: int):
        n = arr.size
        cs = np.concatenate([[0.0], np.cumsum(arr)])
        out = np.empty(n)
        for i in range(n):
            start = max(0, i - (window - 1))
            window_sum = cs[i + 1] - cs[start]
            count = i - start + 1
            out[i] = window_sum / count
        return out

    # Calculate trailing moving averages (start at index 0)
    ma_50 = trailing_ma(price, 50)
    ma_200 = trailing_ma(price, 200)

    # Visual separation: for demonstration clarity, slightly offset the
    # first ~20 days of the 50-day MA so it does not overlap the 200-day MA
    # at the very beginning (does not change cross calculations later).
    sep_days = 20.0
    ma_50_vis = ma_50.copy()
    msep = x <= sep_days
    if np.any(msep):
        # Smoothly decaying offset from start to zero at sep_days
        t = x[msep] / max(sep_days, 1e-6)
        # Raised-cosine style decay
        decay = 0.5 * (1 + np.cos(np.pi * t))
        sep_amp = 0.8  # amplitude of initial visual separation in price units
        ma_50_vis[msep] = ma_50_vis[msep] + sep_amp * decay

    # Plot
    ax.plot(x, price, linewidth=1, color='lightgray', label='Price', alpha=0.7, zorder=1)
    line200, = ax.plot(x, ma_200, linewidth=2.5, color='#2E86AB', label='200-day MA', zorder=2, alpha=0.9)
    line50, = ax.plot(x, ma_50_vis, linewidth=2.8, color='#FFA500', label='50-day MA', zorder=3)
    # Make 50-day MA visually pop when overlapping early on
    line50.set_path_effects([pe.Stroke(linewidth=4.2, foreground='white', alpha=0.9), pe.Normal()])
    # Add small start markers at day 0 so both starts are obvious
    ax.plot(x[0], ma_200[0], marker='o', color='#2E86AB', markersize=5, markeredgecolor='white', zorder=3)
    ax.plot(x[0], ma_50_vis[0], marker='o', color='#FFA500', markersize=6, markeredgecolor='white', zorder=4)

    # Mark golden cross
    # Cross detection on full range (both MAs defined everywhere for trailing)
    # Choose crosses closest to the requested positions: ~35 (death), ~70 (golden)
    target_death = 32.0
    target_golden = 70.0

    # Golden cross (50 above 200)
    golden_cross_idx = np.where((ma_50[1:] > ma_200[1:]) & (ma_50[:-1] <= ma_200[:-1]))[0]
    if len(golden_cross_idx) > 0:
        # pick cross closest to target_golden
        idx = golden_cross_idx[np.argmin(np.abs(x[golden_cross_idx] - target_golden))]
        ax.plot(x[idx], ma_50[idx], 'go', markersize=12, label='Golden Cross')
        ax.annotate('Golden Cross\n(Bullish)', xy=(x[idx], ma_50[idx]),
                    xytext=(x[idx] - 30, ma_50[idx] + 8),
                    fontsize=10, fontweight='bold',
                    bbox=dict(boxstyle='round,pad=0.5', facecolor='lightgreen', alpha=0.8),
                    arrowprops=dict(arrowstyle='->', color='green', lw=2))

    # Mark death cross
    death_cross_idx = np.where((ma_50[1:] < ma_200[1:]) & (ma_50[:-1] >= ma_200[:-1]))[0]
    if len(death_cross_idx) > 0:
        # pick cross closest to target_death
        idx = death_cross_idx[np.argmin(np.abs(x[death_cross_idx] - target_death))]
        ax.plot(x[idx], ma_50[idx], 'ro', markersize=12, label='Death Cross')
        ax.annotate('Death Cross\n(Bearish)', xy=(x[idx], ma_50[idx]),
                    xytext=(x[idx] + 20, ma_50[idx] - 8),
                    fontsize=10, fontweight='bold',
                    bbox=dict(boxstyle='round,pad=0.5', facecolor='lightcoral', alpha=0.8),
                    arrowprops=dict(arrowstyle='->', color='red', lw=2))

    ax.set_xlabel('Time (Days)', fontsize=12)
    ax.set_ylabel('Price', fontsize=12)
    ax.set_title('Moving Average Crossovers', fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'moving-averages.png'), dpi=300, bbox_inches='tight')
    print("Generated: moving-averages.png")
    plt.close()


def main():
    """Generate all chart patterns."""
    print("Generating technical analysis chart patterns...")
    print(f"Output directory: {OUTPUT_DIR}")
    print("-" * 50)
    
    generate_head_and_shoulders()
    generate_double_top_bottom()
    generate_support_resistance()
    generate_cup_and_handle()
    generate_flag_pennant()
    generate_moving_averages()
    
    print("-" * 50)
    print("All chart patterns generated successfully!")


if __name__ == "__main__":
    main()
