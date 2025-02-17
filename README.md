## Description

RadoNumbers is a computational mathematics project focused on generating previously unknown three-colour, three-term Rado numbers using SAT solvers (such as Kissat and CaDiCaL). Additionally, we have developed an automated case-based approach to prove lower bounds for these numbers.

## Usage

To run the program, execute one of the following shell scripts depending on your preference:

- **For incremental Rado number generation**, use the `incremental_driver.sh` script:
  1. Make the script executable:
     ```bash
     chmod +x incremental_driver.sh
     ```
  2. Run the script:
     ```bash
     ./incremental_driver.sh <result> <a> <b> <c>
     ```

- **For non-incremental Rado number generation**, use the `nonincremental_driver.sh` script:
  1. Make the script executable:
     ```bash
     chmod +x nonincremental_driver.sh
     ```
  2. Run the script:
     ```bash
     ./nonincremental_driver.sh <result> <a> <b> <c> <mode>
     ```
