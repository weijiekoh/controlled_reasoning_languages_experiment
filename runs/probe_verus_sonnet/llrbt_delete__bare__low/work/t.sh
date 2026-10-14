#!/bin/bash
cd /work; ./build.sh; verus llrbt_delete.rs 2>&1 | grep -v "^$" | head -${1:-60}
