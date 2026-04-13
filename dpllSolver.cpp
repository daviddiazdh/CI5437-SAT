#include <stdio.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <cmath>
#include <fstream>
#include <string>

using namespace std;

enum SAT_STATE{
    SAT,
    NSAT,
    NDET
};

enum PURE_STATE{
    UNSET,
    POS,
    NEG,
    IMPURE
};

struct VARIABLE_STATE{
    PURE_STATE ps;
    vector<int> pos_clauses;
    vector<int> neg_clauses;
};

enum MODEL_STATE{ 
    NIL, 
    T,
    F
};

SAT_STATE clause_eval(set<int>& clause, vector<MODEL_STATE>& model, vector<PURE_STATE>& pure_symbols, int& symbol_unit_clause){
    SAT_STATE value = NDET;
    bool all_symbols_in_model = true;

    // Para cláusulas unitarias
    int symbols_outside_model = 0;
    int candidate_unit_clause = 0;
    bool unit_clause = true;
    // -------------------------
    
    for(const int & symbol : clause){
        
        MODEL_STATE symbol_state = model[abs(symbol)];
        
        if(symbol_state != NIL){
            if((symbol > 0 && symbol_state == T) || (symbol < 0 && symbol_state == F)){
                value = SAT;
                return value;
            }
        } else {
            all_symbols_in_model = false;
        }
    }

    for(const int& symbol : clause){
        MODEL_STATE symbol_state = model[abs(symbol)];
        
        // Verificación del caso de símbolos puros
        if(symbol_state == NIL){
            PURE_STATE state = pure_symbols[abs(symbol) - 1];
            if(state == UNSET && symbol > 0){
                pure_symbols[abs(symbol) - 1] = POS;
            } else if(state == UNSET && symbol < 0){
                pure_symbols[abs(symbol) - 1] = NEG;
            } else if((symbol > 0 && state == NEG) || (symbol < 0 && state == POS)){
                pure_symbols[abs(symbol) - 1] = IMPURE;
            }
        }

        // Verificación de claúsula unitaria
        if(symbol_state != NIL){
            if((symbol > 0 && symbol_state == T) || (symbol < 0 && symbol_state == F)){
                unit_clause = false;
            }
        } else {
            symbols_outside_model++;
            candidate_unit_clause = symbol;
            if(symbols_outside_model > 1){
                unit_clause = false;
            }
        }

    } 

    if(unit_clause && symbols_outside_model == 1){
        symbol_unit_clause = candidate_unit_clause;
    }

    if(all_symbols_in_model) return NSAT;
    else return NDET;

}

bool dpll(set<set<int>>& clauses, vector<bool>& symbols, vector<MODEL_STATE>& model, int &n){

    SAT_STATE short_circuit = SAT;
    vector<PURE_STATE> pure_symbols(n, UNSET);

    vector<int> unit_clauses_symbols;

    for(set<int> clause : clauses){
        int symbol_unit_clause = 0;
        SAT_STATE eval = clause_eval(clause, model, pure_symbols, symbol_unit_clause);
        if(eval == NSAT){
            return false;
        } else if(eval == NDET){
            short_circuit = NDET;
        }

        if(symbol_unit_clause != 0){
            unit_clauses_symbols.push_back(symbol_unit_clause);
        }
    }
    
    if(short_circuit == SAT){
        return true;
    }

    int index = 1;
    for(PURE_STATE ps : pure_symbols){
        if(ps == POS){
            model[index] = T;
            symbols[index] = false;
            return dpll(clauses, symbols, model, n);
        } else if(ps == NEG){
            model[index] = F;
            symbols[index] = false;
            return dpll(clauses, symbols, model, n);
        }
        index++;
    }

    if(unit_clauses_symbols.size() != 0){
        int unit_clause_symbol = unit_clauses_symbols[0];
        if(unit_clause_symbol >= 0){
            model[unit_clause_symbol] = T;
            symbols[unit_clause_symbol] = false;
            return dpll(clauses, symbols, model, n);
        } else{
            model[-1 * unit_clause_symbol] = F;
            symbols[-1 * unit_clause_symbol] = false;
            return dpll(clauses, symbols, model, n);
        }
    }

    int first = 0;
    while(first < symbols.size()){
        if(first != 0 && symbols[first]){
            break;
        }
        first++;
    }
    symbols[first] = false;
    
    model[first] = T;

    vector<MODEL_STATE> left_model = model;
    vector<bool> left_symbols = symbols;
    bool left_expr = dpll(clauses, left_symbols, left_model, n);
    
    if(left_expr) return true;
    model[first] = F;
    return dpll(clauses, symbols, model, n);

}

bool parse_entry(set<set<int>>& clauses, int& n, string file_str){

    ifstream file(file_str);

    // Verificar si se abrió correctamente
    if (!file.is_open()) {
        cerr << "No se pudo abrir el archivo." << endl;
        return false;
    }

    string word;
    set<int> partial_clause;

    int index = 0;
    while(file >> word){
        if(word == "c"){
            // No leer comentario
            string line;
            getline(file, line);
        } else if(word == "p"){
            string format;
            if(!(file >> format)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            if(format != "cnf"){
                cerr << "Debe enviar una entrada con formato válido, este formato no es CNF" << endl;
                return false;
            } 

            string variables_str;
            if(!(file >> variables_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            try{
                n = stoi(variables_str);
            }catch (const invalid_argument& e) {
                cerr << "Error: Variables no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Variables es demasiado grande para un int." << endl;
                return false;
            }

            string clauses_str;
            if(!(file >> clauses_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            try{
                int clauses_amount = stoi(clauses_str);
            }catch (const invalid_argument& e) {
                cerr << "Error: Clauses no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Clauses es demasiado grande para un int." << endl;
                return false;
            }
        } else if(word == "%"){
            break;
        } else {
            try{
                int symbol = stoi(word);
                
                if(symbol == 0){
                    clauses.insert(partial_clause);
                    partial_clause.clear();
                } else {
                    partial_clause.insert(symbol);
                }

            }catch (const invalid_argument& e) {
                cerr << "Error: Un símbolo dado no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Un símbolo dado es demasiado grande para un int." << endl;
                return false;
            }
        }
    }

    if(!partial_clause.empty()){
        clauses.insert(partial_clause);
    }

    file.close();
    return true;

}


int main(int argc, char* argv[]){

    if(argc != 2){
        cerr << "Error en uso: ./dpllSolver <archivo-cnf>" << endl;
        return 1;
    }

    string cnf_file = argv[1];

    set<set<int>> clauses;  
    // unordered_map<int, set<int>> clausess;
    int n;

    if(!parse_entry(clauses, n, cnf_file)){
        return 1;
    }

    vector<MODEL_STATE> model(n + 1, NIL);
    vector<bool> symbols(n + 1, true);

    bool satisfiable = dpll(clauses, symbols, model, n);

    if(satisfiable) cout << "SATISFIABLE" << endl;
    else cout << "UNSATISFIABLE" << endl;

    return 0;
}