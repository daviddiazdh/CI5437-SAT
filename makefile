CXX = g++
CXXFLAGS = -std=c++17

FILE_DPLL = dpllSolver
FILE_COLORING = coloringSolver
HEADER = DPLL.h

all: compile_dpll compile_coloring

compile_dpll: 
	$(CXX) $(CXXFLAGS) -o $(FILE_DPLL) $(FILE_DPLL).cpp  $(HEADER)

compile_coloring: 
	$(CXX) $(CXXFLAGS) -o $(FILE_COLORING) $(FILE_COLORING).cpp  $(HEADER)

clean:
	rm -f dpllSolver coloringSolver
