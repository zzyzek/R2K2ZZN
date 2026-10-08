# SPDX-License-Identifier: CC0-1.0
# To the extent possible under law, the author has waived all copyright and related or
# neighboring rights to this file. See the LICENSE file (CC0 1.0 Universal).

"""Two-colour Zig-Zag Numberlink on rectangles: decide and solve.

    from zzn import Instance, decide, solve
    inst = Instance(12, 12, (0, 0), (11, 11), (0, 11), (11, 0))
    decide(inst)   # -> False (T1: the endpoints alternate around the border)
    solve(Instance(12, 12, (0, 0), (0, 11), (11, 0), (11, 11)))  # -> (path0, path1)

See README.md and docs/ALGORITHM.md.
"""
from .grid import Instance, check_solution, render, well_formed
from .catalogue import fires
from .ips import acceptable, hamiltonian_path
from .plugdp import solve_paths
from .solver import decide, solve, explain, SolverError

__all__ = ["Instance", "decide", "solve", "explain", "fires", "check_solution", "render",
           "acceptable", "hamiltonian_path", "solve_paths", "well_formed", "SolverError"]
__version__ = "1.0.0"
