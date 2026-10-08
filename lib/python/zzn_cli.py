#!/usr/bin/env python3
# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Command-line front end; see `python3 zzn_cli.py --help`."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zzn.cli import main

sys.exit(main())
