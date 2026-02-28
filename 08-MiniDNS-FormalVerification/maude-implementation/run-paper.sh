#!/bin/bash
# DNS Paper Version Runner

export LD_LIBRARY_PATH=/tmp/maude_runtime/usr/lib/x86_64-linux-gnu:$LD_LIBRARY_PATH
export MAUDE_LIB=/tmp/maude_runtime/usr/share/maude

MAUDE=/tmp/maude_runtime/usr/bin/maude

echo "=========================================="
echo "DNS Formal Verification - Fixed Version"
echo "ETH SIGCOMM 2023 Implementation"
echo "=========================================="
echo ""

# Run with interactive commands
$MAUDE dns-paper-fixed.maude
