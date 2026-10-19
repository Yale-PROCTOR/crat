# The hardware of the paper's times

- **Machine:** an AMD Ryzen 9 9950X (16 cores, 32 threads) with 128 GB of RAM, under Linux.
- **Protocol:** one program at a time on an otherwise idle machine. The wall was measured around the translate pass on the prepared input (GNU time `-v` beside it). One trial per program.
- **c2rust:** the minimum of 3 trials of GNU time around `c2rust transpile`, inside its image (`third-party/`).
- **Peak memory of the translate pass:** lil 90.1 GiB, brotli 33.2 GiB, libzahl 23.9 GiB. Every other program, the eight included, stays at or below 9.5 GiB.
- **The full run** needs a machine with at least 128 GB. Our translate passes take about 2.6 h one after another: 9,133 s for the twenty and 117 s for the eight.
- **`--small`** leaves out lil and brotli, so it fits in 32 GB (peak 23.9 GiB, libzahl). Its translate passes take about 80 min on the machine above: 4,648 s for the eighteen and 117 s for the eight.
- **Reading the times:** they are printed beside the paper's with their ratio and never compared for equality. A container, another processor or a loaded machine changes them.
