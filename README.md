# The Proof of the Faudree–Gyárfás–Schelp–Tuza Conjecture

Zhijun Lu, Chengshuo Qiao, Qirui Ying and Huimin Song.

[Paper](fgst_conjecture.pdf) · [Supplementary Proofs](supplementary.pdf) · [Manuscript release](https://github.com/rewere143-cell/fgst-strong-clique/releases/tag/v1.1.0) · [Verification data](https://github.com/rewere143-cell/fgst-strong-clique/releases/tag/v1.0.0)

The paper derives the bounds for induced five-cycles and the restrictions used at small odd degrees. The supplementary PDF illustrates the individual configurations, gives the case analyses and identifies the inputs for the certificate checks. The [figure scripts](reproducibility/figure_sources/) reconstruct the indicated groups of drawings from the archived inputs. The [proof index](PROOF_NOTES.md) identifies the supporting calculations, and the [verification record](VERIFICATION.md) gives their reference results.

## Compile the paper and supplement

The [paper](source/main.tex) and [supplement](source/supplementary.tex) have separate LaTeX entry points. In the `source` directory, compile `main.tex` with pdfLaTeX, run `bibtex main`, and run pdfLaTeX twice more. Compile `supplementary.tex` three times with pdfLaTeX. If an edit changes numbering, run `python refresh_crossrefs.py` after compiling both documents, then compile both again. Name the PDFs `fgst_conjecture.pdf` and `supplementary.pdf` and keep them together for links in both directions.

## Restore the verification data

Download the three files named `fgst-verification-data-01.zip`, `fgst-verification-data-02.zip` and `fgst-verification-data-03.zip` from the [v1.0.0 data release](https://github.com/rewere143-cell/fgst-strong-clique/releases/tag/v1.0.0). From the repository root, run the following command with Python 3.11 or later. Replace `DOWNLOADS` with the directory containing the three files.

```console
python -B restore_data.py DOWNLOADS
```

This checks each archive and the SHA-256 digest of every restored file against [release-data.json](release-data.json). Each dataset goes in the directory expected by the proof programs. Repeating the command checks files already restored and resumes after an interruption. To verify the archives without extracting the data, append `--verify-only`.

## Verify the bounds

For the uniform bound in simple graphs, use a 64-bit Python environment with a C17 compiler on a little-endian machine. From the repository root run

```console
cd reproducibility
python -B run_all.py --output results/fresh-run
```

The output directory must be new. The [simple-graph verification guide](reproducibility/README.md) gives the commands for the auxiliary odd-degree certificates.

For multigraphs, start in `reproducibility/multigraph/` and run

```console
python -X utf8 -B verify.py hashes
python -X utf8 -B verify.py flags
python -X utf8 -B check_induced_five_cycle.py
python -X utf8 -B verify.py finite --jobs 2
```

The flag calculations require NumPy and SciPy. The finite checks use the included Windows proof checker and temporary disk space for decompression. The [multigraph verification guide](reproducibility/multigraph/REPLAY.md) describes the software, the C checker and the individual cases. [Release scope](RELEASE_SCOPE.md) lists the coverage of the integrity manifests.
