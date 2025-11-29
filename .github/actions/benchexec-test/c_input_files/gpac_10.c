// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Roman Amjaga
//
// SPDX-License-Identifier: Apache-2.0

// https://www.cvedetails.com/cve/CVE-2022-47653/
// repository: https://github.com/gpac/gpac
// commit: 007bf61
// extract of: src/media_tools/av_parsers.c (function: eac3_update_channels)

#include <stdint.h>
#include <string.h>
#include "helpers.c"

typedef struct {
  uint32_t acmod;
} GF_AC3StreamInfo;

typedef struct {
  uint32_t nb_streams;
  GF_AC3StreamInfo streams[8];
} GF_AC3Config;

int main() {
  GF_AC3Config hdr;
  hdr.nb_streams = getNumberInRange(0, 20);
  for (uint32_t i = 0; i < hdr.nb_streams; i++) {
    hdr.streams[i].acmod = i; // Problem: hdr.nb_streams is 10 but hdr.streams length is only 8 that results in stack buffer overflow
  }
}
