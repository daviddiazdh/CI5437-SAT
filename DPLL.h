#ifndef DPLL_H
#define DPLL_H

#include <iostream>
#include <vector>
#include <algorithm>
#include <cmath>

using namespace std;

const int VAL_FREE = 0;
const int VAL_TRUE = 1;
const int VAL_FALSE = -1;

/**
 *  @brief Motor que define el estado del problema en cada marco de la recursión.
 *  
 *  Inicializa las variables del problema (cláusulas, ubicación de símbolos positivos y negativos, 
 *  modelos, cláusulas sin asignar y cláusulas satisfechas).
 */
struct SolverState {
    int num_vars;
    vector<vector<int>> clauses;
    // Cláusulas donde la var aparece positiva
    vector<vector<int>> pos_map; 
    // Cláusulas donde la var aparece negativa
    vector<vector<int>> neg_map; 
    
    vector<int> current_model;
    vector<int> unassigned_in_clause; 
    vector<int> satisfied_in_clause; 

    SolverState(int vars, const vector<vector<int>>& cls) : num_vars(vars), clauses(cls) {
        pos_map.resize(num_vars + 1);
        neg_map.resize(num_vars + 1);
        current_model.assign(num_vars + 1, VAL_FREE);
        unassigned_in_clause.assign(clauses.size(), 0);
        satisfied_in_clause.assign(clauses.size(), 0);
        
        // Inicialización de cláusulas no asignadas (todas) y de cláusulas donde los 
        // símbolos aparecen con signo positivo y negativo (esto facilita la detección de 
        // símbolos puros en la recursión de DPLL)
        for (int i = 0; i < (int)clauses.size(); ++i) {
            unassigned_in_clause[i] = clauses[i].size();
            for (int lit : clauses[i]) {
                int v = abs(lit);
                if (lit > 0) pos_map[v].push_back(i);
                else neg_map[v].push_back(i);
            }
        }
    }
};

/**
 *  @brief Deshace las asignaciones registradas en el historial de este nivel
 *  
 *  Devuelve los cambios en orden contrario al que fueron hechos, de modo que
 *  mantenga el estado original del problema. 
 *  
 *  Para cada variable modificada en el historial en sentido inverso, hace:
 *  
 *  - Toma del historial la variable modificada.
 *  
 *  - Busca su valor en el modelo.
 *  
 *  - Actualiza los estados de las cláusulas donde aparecía dicha variable, tanto
 *    las cláusulas que satisfacía el estado de la variable como las que no.
 *  
 *  - Devuelve el valor de la variable a ```VAL_FREE``` en el modelo.
 *  
 *  @param s Contiene el estado del problema
 *  @param history Guarda las variables que han sido modificadas en orden de tiempo
 *  @note Complejidad Temporal: ```O(|N| * |C|)``` 
 *  @note Complejidad Espacial: ```O(|N| + |C|)``` 
 *  @note con ```N``` el conjunto de variables y ```C``` el conjunto de cláusulas 
 */
void undo_assignments(SolverState& s, const vector<int>& history) {
    for (int i = (int)history.size() - 1; i >= 0; --i) {
        int v = history[i];
        int val = s.current_model[v];

        // Obtención de cláusulas satisfacibles y no satisfacibles por la variable dada
        const auto& t_occs = (val == VAL_TRUE) ? s.pos_map[v] : s.neg_map[v];
        const auto& f_occs = (val == VAL_TRUE) ? s.neg_map[v] : s.pos_map[v];

        // Rollback en las cláusulas satisfechas
        for (int c : t_occs) {
            s.satisfied_in_clause[c]--;
            s.unassigned_in_clause[c]++;
        }
        // Rollback en las cláusulas no satisfechas
        for (int c : f_occs) {
            s.unassigned_in_clause[c]++;
        }
        // Limpiar el valor de la variable en el modelo
        s.current_model[v] = VAL_FREE;
    }
}

/**
 *  @brief Detecta Cláusulas Unitarias y las propaga en cascada.
 *  
 *  Toma un valor de una variable unitaria forzada y se encarga de:
 *  
 *  - Detectar inconsistencias en los modelos para detectar contradicciones.
 *  
 *  - Registra el historial de cambios para deshacerlos en DPLL.
 *  
 *  - Detectar nuevas cláusulas unitarias para seguir reduciendo la expresión,
 *  esto lo hace iterativamente reduciendo la complejidad de tiempo de la recursión.
 *  
 *  @param s Estado del problema en un momento dado
 *  @param start_var Variable a ser evaluada
 *  @param start_val Valor de forzado de la variable
 *  @param history Historial de movimientos hasta el momento (usado solo en DPLL)
 *  @note Complejidad Temporal: ```O(|N| * |C|)``` 
 *  @note Complejidad Espacial: ```O(|N| + |C|)``` 
 *  @note con ```N``` el conjunto de variables y ```C``` el conjunto de cláusulas 
 */
bool unit_clauses_propagation(SolverState& s, int start_var, int start_val, vector<int>& history) {
    vector<int> task_queue;
    task_queue.push_back(start_val == VAL_TRUE ? start_var : -start_var);

    int head = 0;
    while (head < (int)task_queue.size()) {
        int lit = task_queue[head++];
        int v = abs(lit);
        int val = (lit > 0) ? VAL_TRUE : VAL_FALSE;

        if (s.current_model[v] != VAL_FREE) {
            if (s.current_model[v] == val) continue;
            // Se encuentra que la variable estaba ya forzada en el modelo a ser !val,
            // pero también a ser val, por lo que se tiene una expresión no satisfacible.
            return false;
        }

        // Si no hay inconsistencias, se asigna el valor a la variable en el modelo
        s.current_model[v] = val;
        history.push_back(v);

        // Se obtienen la lista de cláusulas que satifacerá este cambio y las que no.
        const auto& t_occs = (val == VAL_TRUE) ? s.pos_map[v] : s.neg_map[v];
        const auto& f_occs = (val == VAL_TRUE) ? s.neg_map[v] : s.pos_map[v];

        // Para toda cláusula satisfacible se aumenta el contador de variables que la satisfacen
        // y se disminuye el contador de variables no asignadas en la cláusula
        for (int c : t_occs) {
            s.satisfied_in_clause[c]++;
            s.unassigned_in_clause[c]--;
        }

        
        bool conflict_found = false;
        for (int c : f_occs) {
            s.unassigned_in_clause[c]--;
            // Caso en el que la cláusula que ninguna variable satisface la cláusula
            if (s.satisfied_in_clause[c] == 0) {
                // Si la cláusula ya no tiene más variables a asignar, entonces no hay variable que la satisfaga
                if (s.unassigned_in_clause[c] == 0) {
                    conflict_found = true;
                } else if (s.unassigned_in_clause[c] == 1) {
                    // Encontrar el literal que queda para la siguiente propagación
                    for (int l : s.clauses[c]) {
                        if (s.current_model[abs(l)] == VAL_FREE) {
                            // Se agrega a las tareas para seguir propagando
                            task_queue.push_back(l);
                            break;
                        }
                    }
                }
            }
        }
        if (conflict_found) return false;
    }
    return true;
}

/**
 *  @brief  Función principal DPLL que maneja el backtracking con detección de símbolos puros y
 *          cláusulas unitarias.
 *  
 *  Primero, hace la detección de símbolos puros y, al encontrar el valor necesario del símbolo puro,
 *  dispara la propagación de cláusulas unitarias con este símbolo definido en el modelo.
 *  En caso de que la propagación de cláusulas unitarias detecte una inconsistencia, devuelve ```false```.
 *  
 *  Luego, evalúa el caso base, si no quedan variables por definir y no se han hallado inconsistencias, 
 *  entonces conseguimos una solución y se retorna ```true```.
 *  
 *  Finalmente, en caso de no darse ninguna de las anteriores, hace backtracking con propagación de
 *  cláusulas unitarias, es decir, prueba un símbolo cualquiera (el primero que no haya sido definido)
 *  y lo añade al modelo con valor ```true```, al finalizar la recursión (si no consiguió resultado) 
 *  devuelve los cambios con ```undo_assignments``` e intenta el caso ```false```.
 *  
 *  @param s Estado del problema en la recursión.
 *  @note Complejidad Temporal: ```O(|N|^2 * |C| * K)``` 
 *  @note Complejidad Espacial: ```O(|N| + |C|)``` 
 *  @note con ```N``` el conjunto de variables, ```C``` el conjunto de cláusulas y K la cantidad de símbolos puros propagados. 
 */
bool DPLL(SolverState& s) {
    vector<int> level_history;

    bool pure_found;
    do {
        pure_found = false;
        for (int i = 1; i <= s.num_vars; ++i) {
            if (s.current_model[i] != VAL_FREE) continue;

            bool appears_pos = false;
            bool appears_neg = false;

            for (int c : s.pos_map[i]) {
                if (s.satisfied_in_clause[c] == 0) { appears_pos = true; break; }
            }
            for (int c : s.neg_map[i]) {
                if (s.satisfied_in_clause[c] == 0) { appears_neg = true; break; }
            }

            if (appears_pos && !appears_neg) {
                if (!unit_clauses_propagation(s, i, VAL_TRUE, level_history)) {
                    undo_assignments(s, level_history);
                    return false;
                }
                pure_found = true;
            } else if (!appears_pos && appears_neg) {
                if (!unit_clauses_propagation(s, i, VAL_FALSE, level_history)) {
                    undo_assignments(s, level_history);
                    return false;
                }
                pure_found = true;
            }
        }
    } while (pure_found);

    // Escoger la próxima variable para el backtracking
    int next_v = 0;
    for (int i = 1; i <= s.num_vars; ++i) {
        if (s.current_model[i] == VAL_FREE) { next_v = i; break; }
    }

    // Caso base: No quedan más variables y no se halló inconsistencias
    if (next_v == 0) return true;

    // Sección de backtracking con true
    vector<int> history_true;
    if (unit_clauses_propagation(s, next_v, VAL_TRUE, history_true)) {
        if (DPLL(s)) return true;
    }
    undo_assignments(s, history_true);

    // Sección de backtracking con false
    vector<int> history_false;
    if (unit_clauses_propagation(s, next_v, VAL_FALSE, history_false)) {
        if (DPLL(s)) return true;
    }
    undo_assignments(s, history_false);

    // Limpiar símbolos puros de este nivel antes de subir
    undo_assignments(s, level_history);
    return false;
}

#endif