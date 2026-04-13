#include <iostream>
#include <vector>
#include <algorithm>
#include <fstream>
#include <string>
#include <sstream>
#include "DPLL.h"

using namespace std;

/**
 *  @brief  Función que parsea la entrada de un archivo en formato CNF
 *  
 *  @param path Ruta del archivo CNF.
 *  @param vars Vector que registra las variables definidas en el archivo.
 *  @param clauses Vector que registra las cláusulas definidas en el archivo.
 *  @note Complejidad Temporal: ```O(|N| + |C|)``` 
 *  @note Complejidad Espacial: ```O(|N| + |C|)``` 
 *  @note con ```N``` el conjunto de variables, ```C``` el conjunto de cláusulas. 
 */
bool load_cnf(const string& path, int& vars, vector<vector<int>>& clauses) {
    ifstream file(path);
    if (!file.is_open()) return false;

    string line;
    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            stringstream ss(line);
            string t; int cls_count;
            ss >> t >> t >> vars >> cls_count;
            clauses.reserve(cls_count);
            break;
        }
    }

    vector<int> current;
    int lit;
    while (file >> lit) {
        if (lit == 0) {
            if (!current.empty()) { clauses.push_back(current); current.clear(); }
        } else {
            current.push_back(lit);
        }
    }
    return true;
}

int main(int argc, char* argv[]) {
    if (argc < 2) { cout << "Uso: ./dpllSolver <archivo.cnf>" << endl; return 1; }

    int num_vars;
    vector<vector<int>> clauses;
    if (!load_cnf(argv[1], num_vars, clauses)) return 1;

    SolverState solver(num_vars, clauses);
    
    // Propagación inicial de cláusulas unitarias del archivo
    vector<int> init_history;
    bool possible = true;
    for (int i = 0; i < (int)clauses.size(); ++i) {
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            if (!unit_clauses_propagation(solver, abs(lit), (lit > 0 ? VAL_TRUE : VAL_FALSE), {init_history})) {
                possible = false;
                break;
            }
        }
    }

    // Ejecución de DPLL solo si antes no se halló una inconsistencia
    if (possible && DPLL(solver)) cout << "SATISFIABLE" << endl;
    else cout << "UNSATISFIABLE" << endl;

    return 0;
}