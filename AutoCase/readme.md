### **AutoCase**

## **1. Introduction**
AutoCase is an automated case prover designed for handling **symbolic interval arithmetic, divisibility constraints, and modular proof generation** in mathematical and combinatorial structures. It utilizes **SymPy** for symbolic computations and implements a structured approach to generating and verifying cases based on interval properties and colour-based partitioning.

---

## **2. Core Components**
AutoCase consists of the following major components:

1. **`colour_case_prover.py`** - Manages interval partitions, colour assignments, proof generation, and case checking.
2. **`interval.py`** - Handles symbolic interval definitions, constraints, and divisibility conditions.
3. **`divisibility.py`** - Implements divisibility logic, ensuring valid number properties in intervals.
4. **`divitems.py`** - Defines `DivItems`, a class to track required and forbidden divisibility constraints.
5. **Example Files** (`example.a.1.1.py` and `example.a.1.1.proof.txt`) - Demonstrate how AutoCase applies its logic to specific cases.

---

## **3. `colour_case_prover.py` - Colour-Based Proof Generation**
This module is responsible for:
- **Storing interval data** and associated properties.
- **Assigning colours** to different intervals.
- **Defining and solving mathematical equations**.
- **Generating feasible colour-based cases**.
- **Generating proof statements** by analyzing divisibility and interval conditions.

### **Key Functions**
#### **Initialization**
```python
class ColorCaseProver:
    def __init__(self):
        self.intervals = dict()
        self.colouring = dict()
        self.equation = list()
        self.substitution = {}
        self.divisibility = Divisibility({})
        self.statement = ""
```
- `intervals`: Stores named interval objects.
- `colouring`: Maps interval names to colour categories.
- `equation`: Stores the primary equation to be solved.
- `substitution`: Tracks symbolic substitutions.

#### **Interval & Colour Management**
- `add_interval(name, interval)`: Assigns named **interval objects**.
- `add_intervals_to_colour(c, names)`: Groups intervals under **colour categories**.

#### **Equation & Proof Generation**
- `generate_cases()`: Produces structured cases based on colour categories.
- `generate_proof(colour_cases)`: Checks interval containment and divisibility constraints, ensuring contradictions.

---

## **4. `interval.py` - Symbolic Interval Representation**
This module defines **interval objects** that store:
- *Symbolic bounds* using `sympy.Interval`.
- *Divisibility properties* (e.g., multiples of \( a^2 \) but not \( a^3 \)).
- *Membership checking* for symbolic values.

### **Key Functions**
#### **Interval Initialization**
```python
class Interval:
    def __init__(self, symbols, interval, divitems, subs):
        self.interval = interval
        self.divitems = divitems
        self.symbols = symbols
        self.subs = subs
        self.min, self.max = self.get_min_max()
```
- Defines an *interval with divisibility conditions*.
- *Computes min/max values* while respecting constraints.

#### **Membership Checking**
- `contains(z):` Ensures \( z \) is inside the interval and checks required divisibility constraints.

---

## **5. `divisibility.py` - Handling Divisibility Conditions**
This module ensures values **satisfy required or forbidden divisibility**.

### **Key Functions**
#### **Check If Expression is Integral**

- `rhs_is_integral(exp, divitems=[]):`: Ensures expressions are **integer values** when needed.

#### **Validate Modulo Constraints**

- `satisfies(exp, divitems=[]):`: **Confirms valid divisibility properties** for interval members.

---

## **6. `divitems.py` - Storing Divisibility Constraints**
Defines **divisibility rules** to check for:
- *Must be divisible by* \( n \).
- *Must NOT be divisible by* \( n \).

### **Example**

- `DivItem(exp, divides)`: Represents divisibility conditions.

---

## **7. Example: Applying AutoCase**
### **Running `example.a.1.1.py`**
This script:
1. *Defines symbolic intervals \( P_0, P_1, ..., P_6 \)*.
2. *Assigns them to sets \( D1, D2, R1, B1, ... \)*.
3. *Initializes the prover* and assigns *colour categories*.
4. *Generates and verifies cases* for an equation.

### **Example Output**
```
Example: For a >= 1, R_3(E(3, 0; a, 1, 1)) >= a^3+5a^2+7a+1.

{0: [{'a': ['x_3 not in D1: x_3 >= a + 1 > a = max(D1)',
            'x_3 not in D2: x_3 <= a*(a + 1) < a**2 + 2*a + 1 = min(D2)',
            'x_3 not in D3: x_3 <= a*(a + 1) < a**3 + 4*a**2 + 4*a + 1 = '
            'min(D3)',
            'x_3 not in D4: x_3 <= a*(a + 1) < a**3 + 5*a**2 + 6*a + 1 = '
            'min(D4)'],
      'x_1': {'in': 'D1', 'range': [1, a]},
      'x_2': {'in': 'D1', 'range': [1, a]},
      'x_3': {'<=': a*(a + 1),
              '>=': a + 1,
              'in': {'D1': False, 'D2': False, 'D3': False, 'D4': False}}},
     {'a': ['x_3 not in D1: x_3 >= a**2 + 3*a + 1 > a = max(D1)',
            'x_3 not in D2: x_3 >= a**2 + 3*a + 1 > a*(a + 3) = max(D2)',
            'x_3 not in D3: x_3 <= a*(2*a + 3) < a**3 + 4*a**2 + 4*a + 1 = '
            'min(D3)',
            'x_3 not in D4: x_3 <= a*(2*a + 3) < a**3 + 5*a**2 + 6*a + 1 = '
            'min(D4)'],
      'x_1': {'in': 'D1', 'range': [1, a]},
      'x_2': {'in': 'D2', 'range': [a**2 + 2*a + 1, a**2 + 3*a]},
      'x_3': {'<=': a*(2*a + 3),
              '>=': a**2 + 3*a + 1,
              'in': {'D1': False, 'D2': False, 'D3': False, 'D4': False}}},
     {'a': ['x_3 not in D1: x_3 >= a**3 + 4*a**2 + 5*a + 1 > a = max(D1)',
            'x_3 not in D2: x_3 >= a**3 + 4*a**2 + 5*a + 1 > a*(a + 3) = '
            'max(D2)',
            'x_3 not in D3: x_3 >= a**3 + 4*a**2 + 5*a + 1 > a*(a**2 + 4*a + '
            '5) = max(D3)',
            'x_3 not in D4: x_3 <= a*(a**2 + 5*a + 5) < a**3 + 5*a**2 + 6*a + '
            '1 = min(D4)'],
      'x_1': {'in': 'D1', 'range': [1, a]},
      'x_2': {'in': 'D3',
              'range': [a**3 + 4*a**2 + 4*a + 1, a**3 + 4*a**2 + 5*a]},
      'x_3': {'<=': a*(a**2 + 5*a + 5),
              '>=': a**3 + 4*a**2 + 5*a + 1,
              'in': {'D1': False, 'D2': False, 'D3': False, 'D4': False}}},

...
...
All cases led to contradiction?: True
```
This confirms that **AutoCase successfully verifies the statement**.

---

## **8. Understanding the Proof Output**

The proof output is verifying that **for all possible cases**, the equation:

\[
R_3(E(3, 0; a, 1, 1)) >= a^3 + 5a^2 + 7a + 1
\]

**holds for all values of \( a >= 1 \)** by **case analysis**.

---

### **8.1. Understanding the Structure of the Proof Output**
The output is structured into cases, where for each case:
- The values of x_1, x_2, x_3 are assigned **intervals** (i.e., which set Di they belong to).
- The proof checks whether **x_3 can exist in any of the defined sets D1, D2, D3, D4**.
- If a contradiction is found (i.e., x_3 cannot be in any Di), that case is ruled out.

### **8.2. Case Structure**
Each case is structured as:
```python
{'a': [
    'x_3 not in D1: ...', 
    'x_3 not in D2: ...', 
    'x_3 not in D3: ...', 
    'x_3 not in D4: ...'],
 'x_1': {'in': 'D1', 'range': [...]},
 'x_2': {'in': 'D2', 'range': [...]},
 'x_3': {
    '<=': ..., 
    '>=': ..., 
    'in': {'D1': False, 'D2': False, 'D3': False, 'D4': False}}}
```
- **Key Observations**:
  - x_3 is checked against all defined sets D1, D2, D3, D4.
  - If all possible locations for x_3 lead to a contradiction, the case is **eliminated**.

---

### **8.3. Step-by-Step Explanation of a Case**
Let's analyze **one case** in detail:

### **Case 1**
```python
{'a': ['x_3 not in D1: x_3 >= a + 1 > a = max(D1)',
       'x_3 not in D2: x_3 <= a*(a + 1) < a**2 + 2*a + 1 = min(D2)',
       'x_3 not in D3: x_3 <= a*(a + 1) < a**3 + 4*a**2 + 4*a + 1 = min(D3)',
       'x_3 not in D4: x_3 <= a*(a + 1) < a**3 + 5*a**2 + 6*a + 1 = min(D4)'],
 'x_1': {'in': 'D1', 'range': [1, a]},
 'x_2': {'in': 'D1', 'range': [1, a]},
 'x_3': {'<=': a*(a + 1),
         '>=': a + 1,
         'in': {'D1': False, 'D2': False, 'D3': False, 'D4': False}}}
```
### **Breaking It Down**
- **x_1 and x_2 belong to D_1** with the range **1 <= x_1, x_2 <= a**.
- **x_3 is expected to be in D1, D2, D3, or D4**.
- The proof checks whether **x_3 can belong to any D_i**:
  - **x_3 not in D1:** Because x_3 >= a+1 > a, which contradicts the maximum of D1.
  - **x_3 not in D2:** Because x_3 <= a(a+1), which is smaller than the minimum of D2.
  - **x_3 not in D3:** Similarly, x_3 does not fit within D3's range.
  - **x_3 not in D4:** Again, x_3 is too small.

**Conclusion for this case**: **x_3 cannot exist in any defined Di, so this case leads to contradiction.**

---


### **8.4. Final Conclusion**
At the end of the proof, the system reports:

```
All cases led to contradiction?: True
```

✔ **This means that in every possible case, the assumptions lead to a contradiction**.  
✔ **Thus, no valid solutions exist**, proving that:

```
R_3(E(3, 0; a, 1, 1)) >= a^3 + 5a^2 + 7a + 1.
```

✔ **The bound is correct for all a >= 1**.

---
