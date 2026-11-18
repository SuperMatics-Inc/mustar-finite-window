"""Plot only the committed certified cell endpoints; no interpolation or search."""
from fractions import Fraction
import json
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap, Normalize
import numpy as np

paper = Path(__file__).resolve().parent.parent
plt.style.use(paper / "figures" / "pub.mplstyle")
plt.rcParams["savefig.bbox"] = None  # Preserve the final journal text width.
fixed_index = json.loads((paper / "scripts" / "certify_threshold.json").read_text())
fixed_frequency = json.loads((paper / "scripts" / "certify_fixed_omega.json").read_text())
index_rows = [row for group in fixed_index for row in group["rows"]]
frequency_rows = [
    dict(lam=int(lam), omega_c=int(window), mu1=cell["u1"], ok=cell["ok"] and group["okG"])
    for lam in ("1", "2", "4", "8")
    for group in [fixed_frequency[lam]]
    for window, cell in group["cells"].items()
]
assert len(index_rows) == 20 and len(frequency_rows) == 16
assert all(row["ok"] for row in index_rows + frequency_rows)

couplings = [1, 2, 4, 8]
blue = plt.rcParams["axes.prop_cycle"].by_key()["color"][0]
cmap = LinearSegmentedColormap.from_list("certified", ["white", blue])
norm = Normalize(0, 2)
fig, axes = plt.subplots(1, 2, figsize=(370.6257 / 72, 2.8), layout="constrained")
for ax, rows, windows, key, xlabel, panel in [
    (axes[0], index_rows, [1, 2, 5, 10, 20], "Nc", r"$N_c$ (fixed index)", "(a)"),
    (axes[1], frequency_rows, [3, 5, 10, 20], "omega_c", r"$\omega_c/\Omega$ (fixed frequency)", "(b)"),
]:
    values = np.empty((len(couplings), len(windows)))
    for row in rows:
        i = couplings.index(row["lam"])
        j = windows.index(row[key])
        endpoint = Fraction(row["mu1"])
        values[i, j] = float(endpoint)
        label = str(endpoint)
        ax.text(j, i, label, ha="center", va="center", fontsize=7.5,
                color="white" if float(endpoint) >= 1.2 else "black")
    image = ax.imshow(values, origin="lower", cmap=cmap, norm=norm, aspect="auto",
                      interpolation="nearest")
    ax.set_xticks(range(len(windows)), windows)
    ax.set_yticks(range(len(couplings)), couplings)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(r"$\lambda$")
    ax.minorticks_off()
    ax.tick_params(length=0, pad=4, labelsize=8.25)
    ax.text(0.02, 1.04, panel, transform=ax.transAxes, ha="left", va="bottom")
cbar = fig.colorbar(image, ax=axes, label=r"Certified limit $u_1$", ticks=[0, 0.5, 1, 1.5, 2],
                    fraction=0.035, pad=0.025)
cbar.ax.tick_params(labelsize=8.25)
fig.savefig(paper / "figures" / "certified-intervals.pdf")
fig.savefig(paper / "figures" / "certified-intervals.png", dpi=180)
print("Generated figures/certified-intervals.pdf and PNG from 36 certified cells")
