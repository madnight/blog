#!/usr/bin/env python3
"""
Generate candlestick pattern visualizations for technical analysis.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import os

# Output directory (relative to this file, independent of CWD)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, '..', 'images'))

def plot_candlestick(ax, x, open_price, high, low, close, width=0.6):
    """Plot a single candlestick."""
    color = 'green' if close >= open_price else 'red'
    edge_color = 'darkgreen' if close >= open_price else 'darkred'
    
    # Draw high-low line
    ax.plot([x, x], [low, high], color=edge_color, linewidth=1.5, solid_capstyle='round')
    
    # Draw body
    body_bottom = min(open_price, close)
    body_height = abs(close - open_price)
    
    rect = Rectangle((x - width/2, body_bottom), width, body_height,
                     facecolor=color, edgecolor=edge_color, linewidth=1.5, alpha=0.8)
    ax.add_patch(rect)


def generate_candlestick_patterns():
    """Generate various candlestick patterns."""
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()
    
    # Pattern 1: Doji
    ax = axes[0]
    x_vals = np.arange(1, 8)
    
    # Regular candles leading to doji
    for i in range(6):
        if i % 2 == 0:
            plot_candlestick(ax, x_vals[i], 48 + i, 52 + i, 46 + i, 50 + i)
        else:
            plot_candlestick(ax, x_vals[i], 50 + i, 52 + i, 46 + i, 48 + i)
    
    # Doji (open = close)
    doji_x = x_vals[6]
    doji_price = 54
    ax.plot([doji_x, doji_x], [doji_price - 3, doji_price + 3], color='black', linewidth=1.5)
    ax.plot([doji_x - 0.2, doji_x + 0.2], [doji_price, doji_price], color='black', linewidth=2)
    
    # Annotate
    ax.annotate('Doji', xy=(doji_x, doji_price + 3), xytext=(doji_x, doji_price + 6),
               ha='center', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='black', lw=1.5))
    
    ax.set_xlim(0, 8)
    ax.set_ylim(42, 62)
    ax.set_title('Doji Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    # Pattern 2: Hammer
    ax = axes[1]
    x_vals = np.arange(1, 8)
    
    # Downtrend
    for i in range(5):
        plot_candlestick(ax, x_vals[i], 60 - i*2, 61 - i*2, 56 - i*2, 57 - i*2)
    
    # Hammer (long lower wick, small body at top)
    hammer_x = x_vals[5]
    hammer_close = 51
    hammer_open = 50
    hammer_high = 52
    hammer_low = 44  # Long lower shadow
    
    ax.plot([hammer_x, hammer_x], [hammer_low, hammer_high], color='darkgreen', linewidth=1.5)
    rect = Rectangle((hammer_x - 0.3, hammer_open), 0.6, hammer_close - hammer_open,
                     facecolor='green', edgecolor='darkgreen', linewidth=1.5, alpha=0.8)
    ax.add_patch(rect)
    
    # Recovery
    plot_candlestick(ax, x_vals[6], 50, 54, 49, 53)
    
    # Annotate
    ax.annotate('Hammer', xy=(hammer_x, hammer_low), xytext=(hammer_x - 1, hammer_low - 4),
               ha='center', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='green', lw=1.5))
    
    ax.set_xlim(0, 8)
    ax.set_ylim(40, 65)
    ax.set_title('Hammer Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    # Pattern 3: Bullish Engulfing
    ax = axes[2]
    x_vals = np.arange(1, 8)
    
    # Downtrend
    for i in range(4):
        plot_candlestick(ax, x_vals[i], 58 - i*2, 59 - i*2, 55 - i*2, 56 - i*2)
    
    # Small bearish candle
    plot_candlestick(ax, x_vals[4], 51, 52, 49, 50)
    
    # Large bullish engulfing candle
    engulf_x = x_vals[5]
    plot_candlestick(ax, engulf_x, 49, 56, 48, 55, width=0.7)
    
    # Recovery
    plot_candlestick(ax, x_vals[6], 55, 58, 54, 57)
    
    # Annotate
    ax.annotate('Bullish\nEngulfing', xy=(engulf_x, 52), xytext=(engulf_x + 1.2, 52),
               ha='left', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='lightgreen', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='green', lw=1.5))
    
    ax.set_xlim(0, 8)
    ax.set_ylim(45, 62)
    ax.set_title('Bullish Engulfing Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    # Pattern 4: Bearish Engulfing
    ax = axes[3]
    x_vals = np.arange(1, 8)
    
    # Uptrend
    for i in range(4):
        plot_candlestick(ax, x_vals[i], 45 + i*2, 47 + i*2, 44 + i*2, 46 + i*2)
    
    # Small bullish candle
    plot_candlestick(ax, x_vals[4], 52, 54, 51, 53)
    
    # Large bearish engulfing candle
    engulf_x = x_vals[5]
    plot_candlestick(ax, engulf_x, 54, 55, 48, 49, width=0.7)
    
    # Decline
    plot_candlestick(ax, x_vals[6], 49, 50, 45, 46)
    
    # Annotate
    ax.annotate('Bearish\nEngulfing', xy=(engulf_x, 51), xytext=(engulf_x + 1.2, 51),
               ha='left', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='lightcoral', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='red', lw=1.5))
    
    ax.set_xlim(0, 8)
    ax.set_ylim(42, 58)
    ax.set_title('Bearish Engulfing Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    # Pattern 5: Morning Star
    ax = axes[4]
    x_vals = np.arange(1, 9)
    
    # Downtrend
    for i in range(4):
        plot_candlestick(ax, x_vals[i], 58 - i*2, 59 - i*2, 55 - i*2, 56 - i*2)
    
    # Large bearish candle
    plot_candlestick(ax, x_vals[4], 51, 52, 47, 48)
    
    # Small indecision candle (star)
    star_x = x_vals[5]
    plot_candlestick(ax, star_x, 48, 49, 46, 47.5, width=0.4)
    
    # Large bullish candle
    plot_candlestick(ax, x_vals[6], 48, 54, 47, 53)
    
    # Recovery
    plot_candlestick(ax, x_vals[7], 53, 56, 52, 55)
    
    # Annotate
    ax.annotate('Morning Star', xy=(star_x, 47), xytext=(star_x, 42),
               ha='center', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='yellow', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='orange', lw=1.5))
    
    ax.set_xlim(0, 9)
    ax.set_ylim(40, 62)
    ax.set_title('Morning Star Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    # Pattern 6: Shooting Star
    ax = axes[5]
    x_vals = np.arange(1, 8)
    
    # Uptrend
    for i in range(5):
        plot_candlestick(ax, x_vals[i], 45 + i*2, 47 + i*2, 44 + i*2, 46 + i*2)
    
    # Shooting star (small body at bottom, long upper wick)
    star_x = x_vals[5]
    star_open = 54
    star_close = 53
    star_high = 60  # Long upper shadow
    star_low = 52
    
    ax.plot([star_x, star_x], [star_low, star_high], color='darkred', linewidth=1.5)
    rect = Rectangle((star_x - 0.3, star_close), 0.6, star_open - star_close,
                     facecolor='red', edgecolor='darkred', linewidth=1.5, alpha=0.8)
    ax.add_patch(rect)
    
    # Decline
    plot_candlestick(ax, x_vals[6], 53, 54, 48, 49)
    
    # Annotate
    ax.annotate('Shooting Star', xy=(star_x, star_high), xytext=(star_x, star_high + 3),
               ha='center', fontsize=11, fontweight='bold',
               bbox=dict(boxstyle='round,pad=0.4', facecolor='lightcoral', alpha=0.8),
               arrowprops=dict(arrowstyle='->', color='red', lw=1.5))
    
    ax.set_xlim(0, 8)
    ax.set_ylim(42, 65)
    ax.set_title('Shooting Star Pattern', fontsize=12, fontweight='bold')
    ax.set_xlabel('Time', fontsize=10)
    ax.set_ylabel('Price', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xticks([])
    
    plt.suptitle('Common Candlestick Patterns', fontsize=16, fontweight='bold', y=0.995)
    plt.tight_layout()
    plt.savefig(os.path.join(OUTPUT_DIR, 'candlestick-patterns.png'), dpi=300, bbox_inches='tight')
    print("Generated: candlestick-patterns.png")
    plt.close()


def main():
    """Generate candlestick patterns."""
    print("Generating candlestick patterns...")
    print(f"Output directory: {OUTPUT_DIR}")
    print("-" * 50)
    
    generate_candlestick_patterns()
    
    print("-" * 50)
    print("Candlestick patterns generated successfully!")


if __name__ == "__main__":
    main()
