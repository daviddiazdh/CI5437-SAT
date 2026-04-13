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

/**
 *  @brief Estructura que define las aristas
 */
struct edge { int x, y; };

/**
 *  @brief Estructura que define la salida del problema para la búsqueda binaria
 */
struct search_output {
    int cromatic_number;
    vector<int> model;
};

/**
 *  @brief  Función que traduce el problema de coloración de grafos para un k determinado a 
 *  un problema de SAT resoluble por DPLL.
 *  
 *  @param edges 
 *  @param nodes 
 *  @param k 
 *  @param clauses 
 *  @param num_vars
 *  @note Complejidad Temporal: ```O(|V| * K^2 + |E|)``` 
 *  @note Complejidad Espacial: ```O(|V| * K^2 + |E|)``` 
 *  @note con ```V``` el conjunto de vértices, ```K``` el número de colores y E el conjunto de aristas. 
 */
void coloring_to_sat(vector<edge>& edges, set<int>& nodes, int k, vector<vector<int>>& clauses, int& num_vars) {
    num_vars = nodes.size() * k;
    clauses.clear();

    // Traducción basada en restricciones:
    // - Cada nodo debe tener al menos un color
    for (int node : nodes) {
        vector<int> clause;
        for (int c = 1; c <= k; ++c) clause.push_back((node - 1) * k + c);
        clauses.push_back(clause);
    }

    // - Nodos adyacentes no pueden tener el mismo color
    for (const auto& e : edges) {
        for (int c = 1; c <= k; ++c) {
            clauses.push_back({-((e.x - 1) * k + c), -((e.y - 1) * k + c)});
        }
    }

    // - Un nodo no puede tener dos colores.
    // Esta condición no está incluida en las láminas de descripción del proyecto, 
    // sin embargo, decidimos añadirlas porque (a pesar de agregar más cláusulas)
    // ayuda a podar el árbol de búsqueda, dado que al asignar un color a un vértice, 
    // podemos dar por hecho que todos los demás colores son falsos (obviamente, esto es
    // responsabilidad de DPLL)
    for (int node : nodes) {
        for (int c1 = 1; c1 <= k; ++c1) {
            for (int c2 = c1 + 1; c2 <= k; ++c2) {
                clauses.push_back({-((node - 1) * k + c1), -((node - 1) * k + c2)});
            }
        }
    }
}

/**
 *  @brief  Función que ejecuta la búsqueda binaria para determinar el número cromático de un grafo
 *  traduciendo el problema a un problema SAT y variando el color k.
 *  
 *  @param lower_bound
 *  @param upper_bound
 *  @param last_k
 *  @param last_model 
 *  @param edges
 *  @param nodes
 *  @note Complejidad Temporal: ```O((|V| * K^2 + |E|) * log|K|)``` 
 *  @note Complejidad Espacial: ```O(|V| * K^2 + |E|)``` 
 *  @note con ```V``` el conjunto de vértices, ```K``` el número de colores y E el conjunto de aristas.
 */
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

/**
 *  @brief  Función que parsea la entrada en formato EDGE de DIMACS y registra las variables y aristas
 *  
 *  @param edges Arreglo de aristas donde se guardarán las aristas
 *  @param nodes Arreglo de vértices donde se guardarán los vértices
 *  @param file_str Ruta del archivo en formato EDGE
 *  @note Complejidad Temporal: ```O(|V| + |E|)``` 
 *  @note Complejidad Espacial: ```O(|V| + |E|)``` 
 *  @note con ```V``` el conjunto de vértices y E el conjunto de aristas.
 */
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

    // Impresión del tiempo de duración del algoritmo
    int ms = chrono::duration_cast<chrono::milliseconds>(end - start).count();
    double total_s = static_cast<double>(ms) / 1000.0;
    int m = total_s / 60;
    double s_restantes = total_s - (m * 60);
    double trunc_s = floor(s_restantes * 1000.0) / 1000.0;
    cout << m << "m" << trunc_s << "s" << endl;

    return 0;
}