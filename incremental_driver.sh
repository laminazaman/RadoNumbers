#!/bin/bash

install_dependencies() {

    if ! python -c "import pysat" &> /dev/null; then
        echo "PySAT is not installed. Installing..."
        pip install python-sat
    fi

}

ensure_directories() {

    if [ ! -d "cadical_log" ]; then
        mkdir cadical_log
    fi

    if [ ! -d "cadical_log/log" ]; then
        mkdir cadical_log/log
    fi

    if [ ! -d "cadical_log/sat" ]; then
        mkdir cadical_log/sat
    fi

}

run_rado_solver() {

    echo "Running..."
    python rado_solver.py "$1" "$2" "$3"

}

install_dependencies
ensure_directories

a=$1
b=$2
c=$3

if [ $# -ne 3 ]; then
    echo "Usage: $0 <a> <b> <c>"
    exit 1
fi

run_rado_solver "$a" "$b" "$c"

echo "Complete."
