# Bitcoin Header Validation using Nova
 
This repo contains circuits for validating Bitcoin headers using [Nova](https://github.com/microsoft/Nova). At each step, it allows validating multiple headers. For each header, the following checks are performed:

- The current header contains the hash of the previous block header.
- The current header hash falls below the PoW target threshold. The 32-bit `nBits` field is converted to a target with 224 significant bits before this check.
- The `nBits` field has been updated correctly if the block height is a multiple of 2016.
- The current header timestamp is greater than or equal to the median of the previous 11 block timestamps.

In addition to the above checks, the circuit also accumulates the chainwork of each block.

**Acknowledgement**: This implementation is heavily inspired by the techniques used by the [ZeroSync](https://github.com/ZeroSync/ZeroSync) project to validate Bitcoin headers.

> [!WARNING]
> This code has not been audited. Use with care.

## Running the examples

There are two examples which demonstrate the header validation.

- `validate_btc_headers` validates one header per Nova step. It takes a file containing the headers as the first argument and the number of headers to validate (starting from the genesis block) as the second argument. It can be run as follows.
    ```
    cargo run -r --example validate_btc_header_batch scripts/headers_100000.txt 10
    ```
- `validate_btc_header_batch` validates multiple headers per Nova step. It takes a file containing the headers as the first argument, the number of headers to validate per step as the second argument, and the number of steps as the third argument.
    ```
    cargo run -r --example validate_btc_header_batch scripts/headers_100000.txt 2 5
    ```


## Generating logs
This repository has three shell scripts to measure peak memory usage and to log the output of the two examples to text files. Build the examples using `cargo build -r --examples` before running these scripts.  The scripts have been tested only on Debian/Ubuntu. The logs will be creates in the `logs` directory.

- `genlog.sh` runs the `validate_btc_headers` example. It takes the number of headers to validate as an argument. This number can be at most 100k since the file containing the headers in the `scripts` directory only has 100k headers. For example, to validate the first 10 headers you can run the following command.
  ```bash
  ./genlog.sh 10
  ```
  The above command will create files `logs/output_10.txt` and `logs/time_output_10.txt`.
- `genlog_batch.sh` runs the `validate_btc_header_batch` example. It takes the number of headers to validate per step as the first argument and the number of steps as the second argument. The product of these arguments can be at most 100k. For example, to validate the first 10 headers in 5 steps with 2 headers validated per step you can run the following command.

  ```bash
  ./genlog_batch.sh 2 5
  ```
  The above command will create files `logs/output_2_5.txt` and `logs/time_output_2_5.txt`.
- `genlog_1024.sh` runs the `validate_btc_header_batch` example 8 times. In each iteration, it validates 1024 headers but varies the number of headers validated per step in the set `{1,2,4,8,16,32,64,128}`. The goal is to study the change in proving time, memory usage, and public parameters size as the number of headers per step increases. The script does not take any parameters and can be run as follows.
  ```bash
  ./genlog_1024.sh
  ```

  > [!NOTE]
  > This repository has a branch called `arecibo` which uses Argument Computer's [fork](https://github.com/argumentcomputer/arecibo) of Nova to perform the Bitcoin header validation. This fork has an implementation of [CycleFold](https://eprint.iacr.org/2023/1192). The shell scripts  files in the `arecibo` branch will create files in the `logs` directory with a prefix `arecibo_` in their filenames.

## Existing benchmarks
The existing files in the `logs` directory were generated on a Dell Precision 3260 desktop with a [13th Gen Intel i7-13700 CPU](https://www.intel.com/content/www/us/en/products/sku/230490/intel-core-i713700-processor-30m-cache-up-to-5-20-ghz/specifications.html) and 32 GB of RAM. The CPU has 16 performance cores and 8 efficient cores (24 threads).

### Validating 100K block headers
To validate 100,000 headers, the results when the number of headers per step is 1, 10, and 100 are given below. The following results are for version 0.37.0 of the [Nova](https://github.com/microsoft/Nova) library.

| Number of<br>headers<br>per step | Number<br>of<br>steps | Total<br>proving<br>time | Compressed<br>SNARK<br>proving<br>time | Recursive<br>SNARK<br>proving<br>time | Compressed<br>SNARK<br>verify<br>time | Proof<br>size <br>(bytes) | Peak<br>memory<br>usage | Public<br>parameters<br>size | Public<br>parameters<br>generation<br>time |
|---------------------------------:|----------------------:|--------------------------|---------------------------------------:|---------------------------------------|--------------------------------------:|---------------------------|------------------------:|-----------------------------:|-------------------------------------------:|
|                                1 |                100000 | 4.18 hours               |                                   1.0s | 4.18 hours                            |                                29.1ms | 12608                     |                0.50 GiB |                    40.89 MiB |                                       2.3s |
|                               10 |                 10000 | 1.87 hours               |                                   4.1s | 1.87 hours                            |                                52.9ms | 13736                     |                2.64 GiB |                   254.66 MiB |                                      14.2s |
|                              100 |                  1000 | 1.46 hours               |                                  36.3s | 1.46 hours                            |                               532.7ms | 15240                     |               19.23 GiB |                     2.53 GiB |                                     210.5s |

The following results are for commit [3ff41aca](https://github.com/argumentcomputer/arecibo/tree/3ff41acaaddf82abe00926ae353c26ad84d726c4) (July 1, 2024) of the [arecibo](https://github.com/argumentcomputer/arecibo) library. The proving times and peak memory usage are smaller when the number of headers per step is 1 and 10. When the number of headers per step is 100, the Nova library has smaller values. The public parameter sizes are smaller for the Nova library in all three cases.

| Number of<br>headers<br>per step | Number<br>of<br>steps | Total<br>proving<br>time | Compressed<br>SNARK<br>proving<br>time | Recursive<br>SNARK<br>proving<br>time | Compressed<br>SNARK<br>verify<br>time | Proof<br>size <br>(bytes) | Peak<br>memory<br>usage | Public<br>parameters<br>size | Public<br>parameters<br>generation<br>time |
|---------------------------------:|----------------------:|--------------------------|---------------------------------------:|---------------------------------------|--------------------------------------:|---------------------------|------------------------:|-----------------------------:|-------------------------------------------:|
| 1                                | 100000                | 3.19 hours               | 0.8s                                   | 3.19 hours                            | 21.2ms                                | 12672                     | 0.44 GiB                | 48.89 MiB                    | 1.3s                                       |
| 10                               | 10000                 | 1.77 hours               | 3.4s                                   | 1.77 hours                            | 52.7ms                                | 13800                     | 2.41 GiB                | 318.66 MiB                   | 5.1s                                       |
| 100                              | 1000                  | 1.78 hours               | 31.5s                                  | 1.78 hours                            | 566.1ms                               | 15304                     | 24.78 GiB               | 3.53 GiB                     | 55.2s                                      |

### Validating 1024 block headers
To validate 1024 headers, the results when the number of headers per step is in the set {1,2,4,8,16,32,64,128} are given below. The following results are for version 0.37.0 of the [Nova](https://github.com/microsoft/Nova) library.

| Number of<br>headers<br>per step | Number<br>of<br>steps | Total<br>proving<br>time | Compressed<br>SNARK<br>proving<br>time | Recursive<br>SNARK<br>proving<br>time | Compressed<br>SNARK<br>verify<br>time | Proof<br>size <br>(bytes) | Peak<br>memory<br>usage | Public<br>parameters<br>size | Public<br>parameters<br>generation<br>time |
|---------------------------------:|----------------------:|-------------------------:|---------------------------------------:|--------------------------------------:|--------------------------------------:|---------------------------|------------------------:|-----------------------------:|-------------------------------------------:|
| 1                                | 1024                  | 153.1s                   | 0.9s                                   | 152.1s                                | 26.1ms                                | 12608                     | 0.42 GiB                | 40.89 MiB                    | 2.3s                                       |
| 2                                | 512                   | 110.8s                   | 1.3s                                   | 109.4s                                | 30.6ms                                | 12984                     | 0.66 GiB                | 65.53 MiB                    | 4.0s                                       |
| 4                                | 256                   | 87.1s                    | 2.1s                                   | 84.8s                                 | 37.4ms                                | 13360                     | 1.23 GiB                | 114.81 MiB                   | 7.4s                                       |
| 8                                | 128                   | 74.9s                    | 3.7s                                   | 71.0s                                 | 45.7ms                                | 13736                     | 2.12 GiB                | 213.38 MiB                   | 14.0s                                      |
| 16                               | 64                    | 69.0s                    | 6.5s                                   | 62.2s                                 | 75.3ms                                | 14112                     | 2.89 GiB                | 410.50 MiB                   | 27.3s                                      |
| 32                               | 32                    | 67.5s                    | 11.5s                                  | 55.4s                                 | 142.7ms                               | 14488                     | 5.67 GiB                | 804.76 MiB                   | 54.6s                                      |
| 64                               | 16                    | 72.7s                    | 22.2s                                  | 49.5s                                 | 292.6ms                               | 14864                     | 11.16 GiB               | 1.56 GiB                     | 105.9s                                     |
| 128                              | 8                     | 91.5s                    | 44.7s                                  | 44.7s                                 | 573.8ms                               | 15240                     | 22.22 GiB               | 3.10 GiB                     | 215.9s                                     |


The following results are for commit [3ff41aca](https://github.com/argumentcomputer/arecibo/tree/3ff41acaaddf82abe00926ae353c26ad84d726c4) (July 1, 2024) of the [arecibo](https://github.com/argumentcomputer/arecibo) library. The proving times and peak memory usage are smaller when the number of headers per step is 1, 2, 4, or 8. When the number of headers per step is 16, 32, 64, or 128, the Nova library has smaller values. The public parameter sizes are smaller for the Nova library in all eight cases.

| Number of<br>headers<br>per step | Number<br>of<br>steps | Total<br>proving<br>time | Compressed<br>SNARK<br>proving<br>time | Recursive<br>SNARK<br>proving<br>time | Compressed<br>SNARK<br>verify<br>time | Proof<br>size <br>(bytes) | Peak<br>memory<br>usage | Public<br>parameters<br>size | Public<br>parameters<br>generation<br>time |
|---------------------------------:|----------------------:|-------------------------:|---------------------------------------:|--------------------------------------:|--------------------------------------:|---------------------------|------------------------:|-----------------------------:|-------------------------------------------:|
| 1                                | 1024                  |                   116.0s |                                   0.8s |                                114.9s |                                21.4ms | 12672                     |                0.37 GiB |                    48.89 MiB |                                       1.3s |
| 2                                | 512                   |                    87.3s |                                   1.1s |                                 85.7s |                                23.3ms | 13048                     |                0.63 GiB |                    81.53 MiB |                                       1.8s |
| 4                                | 256                   |                    74.2s |                                   1.7s |                                 71.7s |                                28.1ms | 13424                     |                1.06 GiB |                   146.81 MiB |                                       2.8s |
| 8                                | 128                   |                    70.0s |                                   2.9s |                                 65.6s |                                47.5ms | 13800                     |                2.03 GiB |                   277.38 MiB |                                       4.8s |
| 16                               | 64                    |                    72.6s |                                   5.2s |                                 64.5s |                                88.6ms | 14176                     |                3.80 GiB |                   538.50 MiB |                                       8.3s |
| 32                               | 32                    |                    73.9s |                                   9.9s |                                 58.2s |                               151.9ms | 14552                     |                7.46 GiB |                     1.04 GiB |                                      15.3s |
| 64                               | 16                    |                    81.0s |                                  19.2s |                                 50.5s |                               306.4ms | 14928                     |               14.33 GiB |                     2.06 GiB |                                      30.1s |
| 128                              | 8                     |                   106.8s |                                  37.6s |                                 46.7s |                               631.8ms | 15304                     |               27.62 GiB |                     4.10 GiB |                                      54.6s |
## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.