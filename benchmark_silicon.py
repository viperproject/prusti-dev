#!/usr/bin/python3

import sys
import argparse

def run_silicon():
    """
    java
        -Xss1024m -Xmx4024m \\
        -cp viper_tools/backends/viperserver.jar \\
        viper.silicon.SiliconRunner \\
        --z3Exe z3-4.8.7-x64-ubuntu-16.04/bin/z3 \\
        --numberOfParallelVerifiers=1 \\
        --logLevel TRACE \\
        --tempDirectory log/viper_tmp/deadlock \\
        --maskHeapMode \\
        file
    """


def parse_args():
    parser = argparse.ArgumentParser(description="Benchmark Silicon Z3 statistics.")
    parser.add_argument(
        "--viper-server-jar",
        help="path of the Viper server JAR",
    )
#   parser.add_argument(
#       "--csv",
#       help="output path of the CSV file",
#   )
#   parser.add_argument(
#       "--svg",
#       help="output path of the SVG file",
#   )
#   parser.add_argument(
#       "--png",
#       help="output path of the PNG file",
#   )
#   parser.add_argument(
#       "--midi",
#       help="output path of the MIDI file",
#   )
#   parser.add_argument(
#       "--max-instantiations",
#       type=int,
#       help="maximum number of quantifier instantiations to load (default: all)",
#   )
#   parser.add_argument(
#       "--skip-instantiations",
#       type=int,
#       default=0,
#       help="number of *loaded* quantifier instantiations to skip (default: 0)",
#   )
#   parser.add_argument(
#       "--tempo",
#       type=int,
#       default=480,
#       help="beats per minute (default: 480)",
#   )
    return parser.parse_args()

def main():
    args = parse_args()

if __name__ == '__main__':
    main()

