#!/bin/bash
# DNS Maude Implementation Runner

export LD_LIBRARY_PATH=/tmp/maude_runtime/usr/lib/x86_64-linux-gnu:$LD_LIBRARY_PATH
export MAUDE_LIB=/tmp/maude_runtime/usr/share/maude

MAUDE=/tmp/maude_runtime/usr/bin/maude

if [ ! -f "$MAUDE" ]; then
    echo "Maude not found. Installing..."
    cd /tmp
    apt-get download maude libbdd0c2 libtecla1t64 2>/dev/null
    mkdir -p maude_runtime
    for deb in *.deb; do
        dpkg-deb -x "$deb" maude_runtime/ 2>/dev/null
    done
fi

echo "Running DNS Formal Verification in Maude..."
echo "============================================"
$MAUDE dns-complete.maude << 'CMD'
show module DNS-ACTORS .
show rules .
rew normalScenario .
q
CMD
