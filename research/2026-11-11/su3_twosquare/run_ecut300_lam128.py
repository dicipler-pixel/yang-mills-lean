"""Single-run ECUT=300, lambda=128 only. ink, 2026-11-11.

Reuses the ECUT=300 driver from run_ecut300_lam64.py.
Does not touch results_sweep.csv. Writes results_ecut300_lam128.csv and logs to stdout.
"""
import os
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import sys, time, csv, gc
import numpy as np
import theta_gt as tg

ECUT = 300
LAM = 128.0
# 8 workers (the theta_gt.build default). ECUT=300 peaked ~6.4 GiB PSS at λ=64
# and the box is 16 GiB with no swap, shared.
PROCS = 8
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_ecut300_lam128.csv")
GAP250 = 37.948107536580
GAP200 = 39.239918487234


def mem_line(tag=""):
    avail = used = free = None
    try:
        with open("/proc/meminfo") as f:
            d = {}
            for line in f:
                k, v, *rest = line.split()
                d[k.rstrip(":")] = int(v)  # kB
        avail = d.get("MemAvailable", 0) / 1048576
        free = d.get("MemFree", 0) / 1048576
        used = (d.get("MemTotal", 0) - d.get("MemAvailable", 0)) / 1048576
    except Exception as e:
        avail = str(e)
    rss = None
    try:
        with open("/proc/self/status") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    rss = int(line.split()[1]) / 1048576
                    break
    except Exception:
        pass
    # sum RSS of this process tree
    tree = rss or 0.0
    try:
        import subprocess
        out = subprocess.check_output(
            ["ps", "-o", "rss=", "--ppid", str(os.getpid())],
            text=True,
        )
        kids = sum(int(x) for x in out.split() if x.strip()) / 1048576
        tree = (rss or 0.0) + kids
    except Exception:
        kids = None
    print(
        f"[mem] {tag} self_rss={rss:.2f}GiB kids={kids if kids is None else f'{kids:.2f}GiB'} "
        f"tree~{tree:.2f}GiB box_used={used:.2f}GiB avail={avail:.2f}GiB free={free:.2f}GiB",
        flush=True,
    )
    return avail, tree


def main():
    t0 = time.time()
    print(f"start ECUT={ECUT} lambda={LAM} procs={PROCS}", flush=True)
    mem_line("start")
    t_build = time.time()
    st, E, S, T = tg.build(ECUT, lean=True, procs=PROCS, verbose=True)
    build_s = time.time() - t_build
    nstates = len(E)
    nnzT = T.nnz
    print(f"build done states={nstates} nnzT={nnzT} nnz_sym={2*nnzT} build_s={build_s:.1f}", flush=True)
    mem_line("after_build")
    # Drop large intermediates not needed for the eigensolve.
    del st
    tg.HW.clear()
    tg.INDEX.clear()
    gc.collect()
    mem_line("after_clear")

    t_eig = time.time()
    L = tg.levels_T(E, T, LAM, 4)
    eig_s = time.time() - t_eig
    g = float(L[1] - L[0])
    ratio = g / (2 * np.sqrt(3 * LAM))
    d250 = g - GAP250
    d200 = g - GAP200
    total_s = time.time() - t0
    print(
        f"levels E0={L[0]:.12f} E1={L[1]:.12f} E2={L[2]:.12f} E3={L[3]:.12f}",
        flush=True,
    )
    print(
        f"gap={g:.12f} ratio={ratio:.10f} d_vs_250={d250:.12e} d_vs_200={d200:.12e} "
        f"eig_s={eig_s:.1f} total_s={total_s:.1f}",
        flush=True,
    )
    new = not os.path.exists(OUT)
    with open(OUT, "a", newline="") as fh:
        w = csv.writer(fh)
        if new:
            w.writerow(
                [
                    "ECUT",
                    "states",
                    "nnz",
                    "lambda",
                    "E0",
                    "E1",
                    "E2",
                    "E3",
                    "gap",
                    "gap_over_2sqrt3lam",
                    "build_s",
                    "eig_s",
                    "total_s",
                    "d_vs_250",
                    "d_vs_200",
                    "procs",
                ]
            )
        w.writerow(
            [f"{ECUT:.6g}", nstates, 2 * nnzT, LAM]
            + [f"{x:.12f}" for x in L]
            + [
                f"{g:.12f}",
                f"{ratio:.10f}",
                f"{build_s:.1f}",
                f"{eig_s:.1f}",
                f"{total_s:.1f}",
                f"{d250:.12e}",
                f"{d200:.12e}",
                PROCS,
            ]
        )
        fh.flush()
    mem_line("done")
    print("wrote", OUT, flush=True)


if __name__ == "__main__":
    main()
