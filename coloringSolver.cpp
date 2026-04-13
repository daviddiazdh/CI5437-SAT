#include <iostream>
#include <vector>
#include <algorithm>
#include <fstream>
#include <string>
#include <sstream>
#include <cmath>
#include <chrono>
#include <map>
#include <set>
#include "DPLL.h"

using namespace std;

struct edge { int x, y; };

struct search_output {
    int cromatic_number;
    vector<int> model;
};

void coloring_to_sat(vector<edge>& edges, set<int>& nodes, int k, vector<vector<int>>& clauses, int& num_vars) {
    num_vars = nodes.size() * k;
    clauses.clear();

    // 1. Cada nodo debe tener al menos un color
    for (int node : nodes) {
        vector<int> clause;
        for (int c = 1; c <= k; ++c) clause.push_back((node - 1) * k + c);
        clauses.push_back(clause);
    }

    // 2. Un nodo no puede tener dos colores (esto ayuda a podar el árbol)
    for (int node : nodes) {
        for (int c1 = 1; c1 <= k; ++c1) {
            for (int c2 = c1 + 1; c2 <= k; ++c2) {
                clauses.push_back({-((node - 1) * k + c1), -((node - 1) * k + c2)});
            }
        }
    }

    // 3. Nodos adyacentes no pueden tener el mismo color
    for (const auto& e : edges) {
        for (int c = 1; c <= k; ++c) {
            clauses.push_back({-((e.x - 1) * k + c), -((e.y - 1) * k + c)});
        }
    }
}

search_output search(int lower_bound, int upper_bound, int last_k, vector<int> last_model, vector<edge>& edges, set<int>& nodes) {
    if (lower_bound > upper_bound) return {last_k, last_model};

    int m = lower_bound + (upper_bound - lower_bound) / 2;
    int num_vars;
    vector<vector<int>> clauses;
    coloring_to_sat(edges, nodes, m, clauses, num_vars);

    SolverState solver(num_vars, clauses);
    if (DPLL(solver)) {
        return search(lower_bound, m - 1, m, solver.current_model, edges, nodes);
    } else {
        return search(m + 1, upper_bound, last_k, last_model, edges, nodes);
    }
}

bool parse_entry(vector<edge>& edges, set<int>& nodes, int& n, string file_str) {
    ifstream file(file_str);
    if (!file.is_open()) return false;
    string word;
    while (file >> word) {
        if (word == "c") { string line; getline(file, line); }
        else if (word == "p") {
            string format; int e_count;
            file >> format >> n >> e_count;
        } else if (word == "e") {
            int v1, v2;
            file >> v1 >> v2;
            nodes.insert(v1); nodes.insert(v2);
            edges.push_back({v1, v2});
        }
    }
    file.close();
    return true;
}

int main(int argc, char* argv[]) {
    auto start = chrono::steady_clock::now();
    if (argc != 3) { cerr << "Uso: ./coloringSolver <archivo-grafo> <archivo-salida>" << endl; return 1; }

    string edge_file = argv[1];
    string output_str = argv[2];

    vector<edge> edges;
    set<int> nodes;
    int nodes_size;
    if (!parse_entry(edges, nodes, nodes_size, edge_file)) return 1;

    search_output result = search(1, nodes_size, nodes_size, {}, edges, nodes);

    int k = result.cromatic_number;
    cout << "Numero Cromatico: " << k << endl;

    // Escritura de colores
    ofstream out(output_str);
    if (out.is_open()) {
        for (int node : nodes) {
            int color_found = 1;
            for (int c = 1; c <= k; ++c) {
                int var_idx = (node - 1) * k + c;
                if (result.model[var_idx] == VAL_TRUE) {
                    color_found = c;
                    break;
                }
            }
            out << color_found << endl;
        }
        out.close();
    }

    auto end = chrono::steady_clock::now();
    cout << chrono::duration_cast<chrono::milliseconds>(end - start).count() << " ms" << endl;

    return 0;
}