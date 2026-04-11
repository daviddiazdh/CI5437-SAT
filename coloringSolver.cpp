#include <stdio.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <cmath>
#include <fstream>
#include <string>
#include <chrono>

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

struct dpll_output{
    bool satisfiable;
    map<int, bool> model;
};

dpll_output dpll(set<set<int>>& clauses, set<int> symbols, map<int, bool> model, int &n){

    // cout << "---------------------------------------------------------------------" << endl;

    SAT_STATE short_circuit = SAT;
    vector<PURE_STATE> pure_symbols(n, UNSET);

    int symbol_unit_clause = 0;
    vector<int> unit_clauses_symbols;

    for(set<int> clause : clauses){
        SAT_STATE eval = clause_eval(clause, model, pure_symbols, symbol_unit_clause);
        if(eval == NSAT){
            // cout << "No es satisfacible" << endl;
            return {false, {}};
        }
        else if(eval == NDET){
            // cout << "Es no determinada" << endl;
            short_circuit = NDET;
        }

        if(symbol_unit_clause != 0){
            unit_clauses_symbols.push_back(symbol_unit_clause);
        }
    }
    
    if(short_circuit == SAT){
        // cout << "Es satisfacible" << endl;
        return {true, model};
    }

    int index = 1;
    for(PURE_STATE ps : pure_symbols){
        if(ps == POS){
            model.insert({index, true});
            symbols.erase(index);
            // cout << "Es puro: " << index << " mandando true" << endl;
            return dpll(clauses, symbols, model, n);
        } else if(ps == NEG){
            model.insert({index, false});
            symbols.erase(index);
            // cout << "Es puro: " << index << " mandando false" << endl;
            return dpll(clauses, symbols, model, n);
        }
        index++;
    }


    if(unit_clauses_symbols.size() != 0){
        int unit_clause_symbol = unit_clauses_symbols[0];
        if(unit_clause_symbol > 0){
            model.insert({unit_clause_symbol, true});
            symbols.erase(unit_clause_symbol);
            // cout << "Es unitario: " << unit_clause_symbol << " mandando true" << endl;
            return dpll(clauses, symbols, model, n);
        } else{
            model.insert({-1 * unit_clause_symbol, false});
            symbols.erase(-1 * unit_clause_symbol);
            // cout << "Es unitario: " << -1 * unit_clause_symbol << " mandando false" << endl;
            return dpll(clauses, symbols, model, n);
        }
    }

    if((!symbols.empty())){
        
        int first = *symbols.begin();
        // cout << "Este es first: " << first << " mandando true" << endl;
        symbols.erase(first);
        model.insert({first, true});
        dpll_output left_dpll_output = dpll(clauses, symbols, model, n);
        bool left_expr = left_dpll_output.satisfiable;
        model[first] = false;
        if(left_expr) return {true, left_dpll_output.model};
        // cout << "Este es first: " << first << " mandando false" << endl;
        dpll_output right_dpll_output = dpll(clauses, symbols, model, n);
        bool right_expr = right_dpll_output.satisfiable;

        return {left_expr || right_expr, right_dpll_output.model};
    } else {
        return {false, {}};
    }

}

struct edge{
    int x;
    int y;
};

void coloring_to_sat(vector<edge>& edges, set<int>& nodes, set<int>& symbols, set<set<int>>& clauses, int& k, int& n){
    
    for(int node : nodes){
        set<int> partial_clause;
        int iter_color = 1;
        while(iter_color <= k){
            int new_symbol = (node - 1) * k + iter_color;
            // cout << new_symbol << endl;
            symbols.insert(new_symbol);
            partial_clause.insert(new_symbol);
            iter_color++;
        }
        clauses.insert(partial_clause);
    }

    for(edge e : edges){
        int vertex1 = e.x;
        int vertex2 = e.y;
        int iter_color = 1;
        while(iter_color <= k){
            int new_symbol_v1 = -1 * ((vertex1 - 1) * k + iter_color);
            int new_symbol_v2 = -1 * ((vertex2 - 1) * k + iter_color);
            clauses.insert({new_symbol_v1, new_symbol_v2});
            iter_color++;
        }
    }

    n = symbols.size();

}

struct search_ouput{
    int cromatic_number;
    map<int, bool> model;
};

search_ouput search(int lower_bound, int upper_bound, int last_known_coloring, map<int, bool> last_known_model, vector<edge>& edges, set<int>& nodes){

    // Add: set<set<int>> last_known_model

    set<int> symbols;
    set<set<int>> clauses;
    int n;

    if(lower_bound == upper_bound){
        coloring_to_sat(edges, nodes, symbols, clauses, lower_bound, n);
        dpll_output dpll_o = dpll(clauses, symbols, {}, n);
        if(dpll_o.satisfiable){
            return {lower_bound, dpll_o.model};
        } else {
            return {last_known_coloring, last_known_model};
        }
    }

    int m = floor((lower_bound + upper_bound)/2);
    coloring_to_sat(edges, nodes, symbols, clauses, m, n);
    dpll_output dpll_o = dpll(clauses, symbols, {}, n);
    if(dpll_o.satisfiable){
        return search(lower_bound, m - 1, m, dpll_o.model, edges, nodes);
    } else {
        return search(m + 1, upper_bound, last_known_coloring, last_known_model, edges, nodes);
    }
}

bool parse_entry(vector<edge>& edges, set<int>& nodes, int& n, string file_str){

    ifstream file(file_str);

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

            if(format != "edge"){
                cerr << "Debe enviar una entrada con formato válido, este formato no es CNF" << endl;
                return false;
            } 

            string nodes_str;
            if(!(file >> nodes_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            try{
                n = stoi(nodes_str);
                // cout << "n: " << n << endl;
            }catch (const invalid_argument& e) {
                cerr << "Error: Nodes no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Nodes es demasiado grande para un int." << endl;
                return false;
            }

            string edges_str;
            if(!(file >> edges_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            try{
                int edges_amount = stoi(edges_str);
                // cout << "edges_amount: " << edges_amount << endl;
            }catch (const invalid_argument& e) {
                cerr << "Error: Edges no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: Edges es demasiado grande para un int." << endl;
                return false;
            }
            
        } else if (word == "e"){

            string vertex1_str;
            if(!(file >> vertex1_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            int vertex1;

            try{
                vertex1 = stoi(vertex1_str);
                // cout << "vertex1: " << vertex1 << endl;
            }catch (const invalid_argument& e) {
                cerr << "Error: El primer vértice no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: El primer vértice es demasiado grande para un int." << endl;
                return false;
            }

            string vertex2_str;
            if(!(file >> vertex2_str)){
                cerr << "Hay un error en la estructura de la entrada" << endl; 
                return false;
            }

            int vertex2;

            try{
                vertex2 = stoi(vertex2_str);
                // cout << "vertex2: " << vertex2 << endl;
            }catch (const invalid_argument& e) {
                cerr << "Error: El segundo vértice no es un número válido." << endl;
                return false;
            } catch (const out_of_range& e) {
                cerr << "Error: El segundo vértice es demasiado grande para un int." << endl;
                return false;
            }

            nodes.insert(vertex1);
            nodes.insert(vertex2);

            edges.push_back({vertex1, vertex2});

        }
    }

    file.close();

    return true;

}

int main(int argc, char* argv[]){

    auto start = chrono::steady_clock::now();

    if(argc != 3){
        cerr << "Error en uso: ./coloringSolver <archivo-grafo> <archivo-salida>" << endl;
        return 1;
    }

    string edge_file = argv[1];
    string output_str = argv[2];

    ofstream output_file(output_str);

    // Verificar si se puede abrir el archivo de salida
    if (!output_file.is_open()) {
        cerr << "No se pudo abrir el archivo de salida." << endl;
        return false;
    }
    output_file.close();

    vector<edge> edges;
    set<int> nodes;
    int nodes_size;

    if(!parse_entry(edges, nodes, nodes_size, edge_file)){
        return 1;
    }

    search_ouput search_o = search(1, nodes_size, nodes_size, {}, edges, nodes);

    int k = search_o.cromatic_number;
    cout << k << endl;

    map<int, bool> model = search_o.model;

    map<int, int> graph_coloring;

    for (const auto& [symbol, state] : model) {
        // cout << symbol << " : " << state << endl;
        int vertex = ceil(static_cast<double>(symbol) / k);
        // cout << "Vértice: " << vertex << endl;

        auto it = graph_coloring.find(vertex);
        if(it == graph_coloring.end() && state){
            int color = symbol % (k);
            if(color == 0){
                graph_coloring[vertex] = k;
            }else {
                graph_coloring[vertex] = color;
            }
            
        } 
    }

    // cout << "----------------------" << endl;

    ofstream output_file2(output_str);

    // Verificar si se puede abrir el archivo de salida
    if (!output_file2.is_open()) {
        cerr << "No se pudo abrir el archivo de salida." << endl;
        return false;
    }

    for (const auto& [vertex, color] : graph_coloring) {
        output_file2 << color << endl;
    }

    output_file2.close();

    auto end = chrono::steady_clock::now();
    auto elapsed = chrono::duration_cast<chrono::milliseconds>(end - start);

    cout << elapsed.count() << " ms" << endl;
    return 0;
}