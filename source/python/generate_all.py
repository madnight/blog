#!/usr/bin/env python3
"""
Master script to generate all technical analysis chart visualizations.
Runs both chart pattern and candlestick pattern generators.
"""

import subprocess
import os

def main():
    """Generate all chart patterns by running both generator scripts."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    print("=" * 60)
    print("Technical Analysis Chart Pattern Generator")
    print("=" * 60)
    print()
    
    scripts = [
        'generate_chart_patterns.py',
        'generate_candlestick_patterns.py'
    ]
    
    for script in scripts:
        script_path = os.path.join(script_dir, script)
        print(f"\nRunning {script}...")
        print("-" * 60)
        
        try:
            result = subprocess.run(
                ['python3', script_path],
                check=True,
                capture_output=False,
                text=True
            )
            print(f"✓ {script} completed successfully")
        except subprocess.CalledProcessError as e:
            print(f"✗ Error running {script}: {e}")
            return 1
        except FileNotFoundError:
            print(f"✗ Script not found: {script_path}")
            return 1
    
    print()
    print("=" * 60)
    print("All chart patterns generated successfully!")
    print("=" * 60)
    return 0

if __name__ == "__main__":
    exit(main())

