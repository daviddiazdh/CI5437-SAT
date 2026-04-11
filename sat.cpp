#include <stdio.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
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

SAT_STATE clause_eval(set<int>& clause, map<int, bool>& model, vector<PURE_STATE>& pure_symbols, int& symbol_unit_clause){
    SAT_STATE value = NDET;
    bool all_symbols_in_model = true;

    // Para cláusulas unitarias
    int symbols_outside_model = 0;
    int candidate_unit_clause = 0;
    bool unit_clause = true;
    // -------------------------
    
    for(int symbol : clause){
        auto it = model.find(abs(symbol));
        if(it != model.end()){
            bool symbol_value = model[abs(symbol)];
            if((symbol > 0 && symbol_value) || (symbol < 0 && !symbol_value)){
                value = SAT;
            }
        } else {
            all_symbols_in_model = false;
        }

        // Verificación del caso de símbolos puros
        if(it == model.end()){
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
        if(it != model.end()){
            bool symbol_value = model[abs(symbol)];
            if((symbol > 0 && symbol_value) || (symbol < 0 && !symbol_value)){
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

    if(unit_clause){
        symbol_unit_clause = candidate_unit_clause;
    }

    if(value == SAT) return value;

    if(all_symbols_in_model) return NSAT;
    else return NDET;

}

bool dpll(set<set<int>>& clauses, set<int> symbols, map<int, bool> model, int &n){

    cout << "---------------------------------------------------------------------" << endl;

    SAT_STATE short_circuit = SAT;
    vector<PURE_STATE> pure_symbols(n, UNSET);

    int symbol_unit_clause = 0;
    vector<int> unit_clauses_symbols;

    for(set<int> clause : clauses){
        SAT_STATE eval = clause_eval(clause, model, pure_symbols, symbol_unit_clause);
        if(eval == NSAT){
            cout << "No es satisfacible" << endl;
            return false;
        }
        else if(eval == NDET){
            cout << "Es no determinada" << endl;
            short_circuit = NDET;
        }

        if(symbol_unit_clause != 0){
            unit_clauses_symbols.push_back(symbol_unit_clause);
        }
    }
    
    if(short_circuit == SAT){
        cout << "Es satisfacible" << endl;
        return true;
    }

    int index = 1;
    for(PURE_STATE ps : pure_symbols){
        if(ps == POS){
            model.insert({index, true});
            symbols.erase(index);
            cout << "Es puro: " << index << " mandando true" << endl;
            return dpll(clauses, symbols, model, n);
        } else if(ps == NEG){
            model.insert({index, false});
            symbols.erase(index);
            cout << "Es puro: " << index << " mandando false" << endl;
            return dpll(clauses, symbols, model, n);
        }
        index++;
    }


    if(unit_clauses_symbols.size() != 0){
        int unit_clause_symbol = unit_clauses_symbols[0];
        if(unit_clause_symbol > 0){
            model.insert({unit_clause_symbol, true});
            symbols.erase(unit_clause_symbol);
            cout << "Es unitario: " << unit_clause_symbol << " mandando true" << endl;
            return dpll(clauses, symbols, model, n);
        } else{
            model.insert({-1 * unit_clause_symbol, false});
            symbols.erase(-1 * unit_clause_symbol);
            cout << "Es unitario: " << -1 * unit_clause_symbol << " mandando false" << endl;
            return dpll(clauses, symbols, model, n);
        }
    }

    if((!symbols.empty())){
        
        int first = *symbols.begin();
        cout << "Este es first: " << first << " mandando true" << endl;
        symbols.erase(first);
        model.insert({first, true});
        bool left_expr = dpll(clauses, symbols, model, n);
        model[first] = false;
        if(left_expr) return true;
        cout << "Este es first: " << first << " mandando false" << endl;
        bool right_expr = dpll(clauses, symbols, model, n);
        return left_expr || right_expr;
    } else {
        return false;
    }

    

}

bool parse_entry(set<set<int>>& clauses, set<int>& partial_clause, set<int>& symbols, int& n){

    ifstream file("entry.txt");

    // Verificar si se abrió correctamente
    if (!file.is_open()) {
        cerr << "No se pudo abrir el archivo." << endl;
        return false;
    }

    string word;

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
                cout << "n: " << n << endl;
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
                cout << "clauses_amount: " << clauses_amount << endl;
            }catch (const invalid_argument& e) {
                cerr << "Error: Clauses no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Clauses es demasiado grande para un int." << endl;
                return false;
            }
            
        } else {
            try{
                int symbol = stoi(word);
                
                if(symbol == 0){
                    clauses.insert(partial_clause);
                    partial_clause.clear();
                } else {
                    partial_clause.insert(symbol);
                    symbols.insert(abs(symbol));
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

    return true;

}

int main(){

    // Esto lo hará dpll-satisfiable
    // set<set<int>> clauses = {{1},{-1}};
    // set<int> symbols = {1,2,3,4};

    set<set<int>> clauses;
    set<int> partial_clause;
    set<int> symbols;
    int n;

    if(!parse_entry(clauses, partial_clause, symbols, n)){
        return 1;
    }

    if(!partial_clause.empty()){
        clauses.insert(partial_clause);
    }
    
    cout << "Símbolos: " << endl;
    for(int s : symbols){
        cout << s << ", ";
    }
    cout << endl;

    cout << "Cláusulas: " << endl;
    for(set<int> clause : clauses){
        
        for(int s : clause){
            cout << s << ", ";
        }
        cout << endl;
    }

    bool satisfiable = dpll(clauses, symbols, {}, n); 

    if(satisfiable) cout << "SATISFIABLE" << endl;
    else cout << "UNSATISFIABLE" << endl;

}
