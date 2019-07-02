all: mesh_simp mesh_simp_holdkeep halfedge

mesh_simp: mesh_simp.cpp Makefile
	g++ $@.cpp -o $@ -Wall -Wextra -g
	
mesh_simp_holdkeep: mesh_simp_holdkeep.cpp Makefile
	g++ $@.cpp -o $@ -Wall -Wextra -g

halfedge: halfedge.cpp Makefile
	g++ halfedge.cpp -o halfedge -Wall -Wextra -g -std=c++11