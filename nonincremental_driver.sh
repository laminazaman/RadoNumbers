#!/bin/bash

install_dependencies() {

    if [ ! -f kissat/build/kissat ]; then
        echo "Kissat is not installed. Installing..."
        git clone https://github.com/arminbiere/kissat.git
        cd kissat
        ./configure
        make test
        cd ..
    fi

}

ensure_directories() {

    if [ ! -d "logs" ]; then
        mkdir logs
    fi

    if [ ! -d "logs/cnf_files" ]; then
        mkdir logs/cnf_files
    fi

    if [ ! -d "logs/generation_time" ]; then
        mkdir logs/generation_time
    fi

    if [ ! -d "logs/sb_log" ]; then
        mkdir logs/sb_log
    fi

    if [ ! -d "logs/sb_sat" ]; then
        mkdir logs/sb_sat
    fi

}

run_generate_clauses() {

    echo "Generating CNF files..."
    python code/generate_clauses.py $(( $1 - 1 )) "$2" "$3" "$4"
    python code/generate_clauses.py "$1" "$2" "$3" "$4"

}

solve_cnf() {

    sat_file="logs/cnf_files/clauses_$(( $1 - 1 ))_${2}.${3}.${4}.cnf"
    log_file="logs/cnf_files/clauses_${1}_${2}.${3}.${4}.cnf"

    if [[ ! -f "$sat_file" || ! -f "$log_file" ]]; then
        echo "CNF file does not exist."
        exit 1
    fi

    echo "Running Kissat..."
    kissat/build/kissat "$sat_file" > "logs/sb_sat/sat_$(( $1 - 1 ))_${2}.${3}.${4}.txt"
    kissat/build/kissat "$log_file" > "logs/sb_log/log_${1}_${2}.${3}.${4}.txt"

}

check() {
    model=$1
    a=$2
    b=$3
    c=$4
    n=${#model[@]}
    
    for ((i=1; i<=n; i++)); do
        for ((j=1; j<=n; j++)); do

            if [[ "${model[$((i - 1))]}" == "${model[$((j - 1))]}" ]]; then
                zc=$((a * i + b * j))
                yb=$((c * j - a * i))
                xa=$((c * j - b * i))
                
                if ((zc % c == 0)) && ((zc / c >= 1 && zc / c <= n)) && [[ "${model[$((zc / c - 1))]}" == "${model[$((i - 1))]}" ]]; then
                    echo "Monochromatic Solution ($i, $j, $((zc / c))) Found"
                    return
                fi
                
                if ((yb % b == 0)) && ((yb / b >= 1 && yb / b <= n)) && [[ "${model[$((yb / b - 1))]}" == "${model[$((i - 1))]}" ]]; then
                    echo "Monochromatic Solution ($i, $((yb / b)), $j) Found"
                    return
                fi
                
                if ((xa % a == 0)) && ((xa / a >= 1 && xa / a <= n)) && [[ "${model[$((xa / a - 1))]}" == "${model[$((i - 1))]}" ]]; then
                    echo "Monochromatic Solution ($((xa / a)), $i, $j) Found"
                    return
                fi
            fi

        done
    done

    echo ""

}

install_dependencies
ensure_directories

result=$1
a=$2
b=$3
c=$4
mode=$5

if [ $# -ne 5 ]; then
    echo "Usage: $0 <result> <a> <b> <c> <mode>"
    echo "Modes: generate | solve | both"
    exit 1
fi

if [ "$mode" = "generate" ]; then
    run_generate_clauses "$result" "$a" "$b" "$c"
elif [ "$mode" = "solve" ]; then
    solve_cnf "$result" "$a" "$b" "$c"
elif [ "$mode" = "both" ]; then
    run_generate_clauses "$result" "$a" "$b" "$c"
    solve_cnf "$result" "$a" "$b" "$c"
else
    echo ""
fi

grep "^s" logs/sb_sat/sat_$(( result - 1 ))_${a}.${b}.${c}.txt
grep "^s" logs/sb_log/log_${result}_${a}.${b}.${c}.txt

echo "Complete."