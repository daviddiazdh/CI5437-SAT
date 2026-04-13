#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <set>
#include <map>
#include <cmath>
#include <algorithm>

using namespace std;

// Representación de tipos para claridad
typedef int Literal;
typedef vector<Literal> Clause;
typedef vector<Clause> Formula;
typedef map<int, bool> Model;

/**
 * Evalúa el estado de una cláusula dado el modelo actual.
 * Retorna: 1 (True), 0 (False), -1 (Indeterminado/Desconocido)
 */
int getClauseStatus(const Clause& clause, const Model& model) {
    bool has_unassigned = false;
    for (Literal lit : clause) {
        int var = abs(lit);
        if (model.count(var)) {
            bool val = model.at(var);
            // Si el literal es satisfecho por el modelo
            if ((lit > 0 && val) || (lit < 0 && !val)) return 1;
        } else {
            has_unassigned = true;
        }
    }
    return has_unassigned ? -1 : 0;
}

/**
 * Busca un símbolo puro: un símbolo que siempre aparece con la misma polaridad 
 * en todas las cláusulas que aún no han sido satisfechas.
 */
bool findPureSymbol(const vector<int>& symbols, const Formula& clauses, const Model& model, int& P, bool& value) {
    Formula active_clauses;
    for (const auto& c : clauses) {
        if (getClauseStatus(c, model) != 1) active_clauses.push_back(c);
    }

    for (int s : symbols) {
        if (model.count(s)) continue;
        bool pos = false, neg = false;
        for (const auto& c : active_clauses) {
            for (Literal lit : c) {
                if (lit == s) pos = true;
                if (lit == -s) neg = true;
            }
        }
        if (pos != neg) { // Si aparece solo como pos o solo como neg
            P = s;
            value = pos;
            return true;
        }
    }
    return false;
}

/**
 * Busca una cláusula unitaria: una cláusula donde todos los literales han sido 
 * evaluados como falsos excepto uno que no tiene asignación.
 */
bool findUnitClause(const Formula& clauses, const Model& model, int& P, bool& value) {
    for (const auto& c : clauses) {
        if (getClauseStatus(c, model) == 1) continue;
        
        int unassigned_count = 0;
        Literal last_lit = 0;
        bool possible_unit = true;

        for (Literal lit : c) {
            int var = abs(lit);
            if (!model.count(var)) {
                unassigned_count++;
                last_lit = lit;
            } else {
                bool val = model.at(var);
                // Si algún literal ya es true, la cláusula no es unitaria, es satisfecha (ya filtrado arriba)
                if ((lit > 0 && val) || (lit < 0 && !val)) {
                    possible_unit = false;
                    break;
                }
            }
        }

        if (possible_unit && unassigned_count == 1) {
            P = abs(last_lit);
            value = (last_lit > 0);
            return true;
        }
    }
    return false;
}

/**
 * Algoritmo DPLL Recursivo
 */
bool DPLL(Formula clauses, vector<int> symbols, Model model) {
    bool all_true = true;
    for (const auto& c : clauses) {
        int status = getClauseStatus(c, model);
        if (status == 0) return false; // Alguna cláusula es falsa
        if (status != 1) all_true = false;
    }
    if (all_true) return true; // Todas las cláusulas son verdaderas

    int P;
    bool value;

    // Símbolo Puro
    if (findPureSymbol(symbols, clauses, model, P, value)) {
        vector<int> next_symbols;
        for (int s : symbols) if (s != P) next_symbols.push_back(s);
        Model next_model = model;
        next_model[P] = value;
        return DPLL(clauses, next_symbols, next_model);
    }

    // Cláusula Unitaria
    if (findUnitClause(clauses, model, P, value)) {
        vector<int> next_symbols;
        for (int s : symbols) if (s != P) next_symbols.push_back(s);
        Model next_model = model;
        next_model[P] = value;
        return DPLL(clauses, next_symbols, next_model);
    }

    // División (Splitting)
    P = symbols[0];
    vector<int> rest(symbols.begin() + 1, symbols.end());
    
    Model model_true = model; model_true[P] = true;
    if (DPLL(clauses, rest, model_true)) return true;

    Model model_false = model; model_false[P] = false;
    return DPLL(clauses, rest, model_false);
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        cerr << "Uso: ./dpllSolver <archivo-cnf>" << endl;
        return 1;
    }

    ifstream file(argv[1]);
    if (!file.is_open()) return 1;

    Formula clauses;
    set<int> symbol_set;
    string line;

    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c' || line[0] == 'p') continue;
        stringstream ss(line);
        int lit;
        Clause c;
        while (ss >> lit && lit != 0) {
            c.push_back(lit);
            symbol_set.insert(abs(lit));
        }
        if (!c.empty()) clauses.push_back(c);
    }

    vector<int> symbols(symbol_set.begin(), symbol_set.end());
    
    if (DPLL(clauses, symbols, Model())) {
        cout << "SATISFIABLE" << endl;
    } else {
        cout << "UNSATISFIABLE" << endl;
    }

    return 0;
}