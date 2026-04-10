#include <stdio.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <cmath>

using namespace std;

// fun is_clause_true(clause, &array is_pure, modelo)
//         enum value = SAT | NSAT | NDET
//         value = NDET
//         all_symbols_in_model = true
//         para cada symbol en clause:
//             si |symbol| está en modelo, entonces 
//                 si (symbol > 0 y symbol == true) || (symbol < 0 y symbol == false), entonces
//                     value = SAT
//                     break
//             si no, entonces
//                 all_symbols_in_model = false
            
//             -----------------------------------------
//             si symbol no está en modelo, entonces
//                 si is_pure(|symbol|) == UNSET, entonces
//                     si symbol > 0, entonces 
//                         is_pure(|symbol|) = POS
//                     si no, entonces 
//                         is_pure(|symbol|) = NEG
//                 si no,
//                     si (symbol > 0 y is_pure(|symbol|) == NEG) o (symbol < 0 y is_pure(|symbol|) == POS), entonces 
//                         is_pure(|symbol|) = IMPURE
//             ------------------------------------------

//         si value == SAT
//             return value

//         si all_symbols_in_model
//             return NSAT
//         else
//             return NDET


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

SAT_STATE clause_eval(set<int>& clause, map<int, bool>& model, vector<PURE_STATE>& pure_symbols){
    SAT_STATE value = NDET;
    bool all_symbols_in_model = true;
    for(int symbol : clause){
        auto it = model.find(abs(symbol));
        if(it != model.end()){
            bool symbol_value = model[abs(symbol)];
            if((symbol > 0 && symbol_value) || (symbol < 0 && !symbol_value)){
                value = SAT;
                break;
            }
        } else {
            all_symbols_in_model = false;
        }

        if(it != model.end()){
            PURE_STATE state = pure_symbols[abs(symbol) - 1];
            if(state == UNSET && symbol > 0){
                pure_symbols[abs(symbol) - 1] = POS;
            } else if(state == UNSET && symbol < 0){
                pure_symbols[abs(symbol) - 1] = NEG;
            } else if((symbol > 0 && state == NEG) || (symbol < 0 && state == POS)){
                pure_symbols[abs(symbol) - 1] = IMPURE;
            }
        }
    } 

    if(value == SAT) return value;

    if(all_symbols_in_model) return NSAT;
    else return NDET;

}


bool dpll(set<set<int>>& clauses, set<int> symbols, map<int, bool> model, int &n){

    SAT_STATE short_circuit = SAT;
    vector<PURE_STATE> pure_symbols(n, UNSET);
    for(set<int> clause : clauses){
        SAT_STATE eval = clause_eval(clause, model, pure_symbols);
        if(eval == NSAT) return false;
        else if(eval == NDET) short_circuit = NDET;
    }
    
    for(PURE_STATE ps : pure_symbols){
        cout << ps << ", ";
    }
    cout << endl;

    if(short_circuit == SAT){
        return true;
    } else {
        cout << "Bien" << endl;
    }

    


    return false;


}

int main(){

    // Esto lo hará dpll-satisfiable
    set<set<int>> clauses = {{1,2},{1,-3},{4,-2}};
    set<int> symbols = {1,2,3,4};
    int n = symbols.size();
    
    bool satisfiable = dpll(clauses, symbols, {{1, true}, {2, true}}, n); 

    cout << satisfiable << endl;

    

    /*
    dpll-satisfiable(s)
        Parsear el input
            - symbols (1..n) 
            - clauses {{1,2,-1}, {1,3,5}, {2}}
        dpll(clauses, symbols, {})
    
    


    dpll(clauses, symbols, model)
        
        enum (UNSET, NEG, POS, IMPURE) array is_pure

        short_circuit = SAT;
        para cada i, clause en clauses:
            si is_clause_true(clause) == NSAT, entonces
                retornar false;
            si no, is_clause_true(clause) == NDET, entonces
                short_circuit = NDET

        si short_circuit == SAT, entonces
            retornar verdadero

        para cada s en is_pure


        
        
    */  
}
