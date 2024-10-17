CC = gcc
CXX = g++
LIBS = -lrt
CFLAGS = --std=c++11 -W -Wall -Wno-sign-compare -O3 -s -pipe -mmmx -msse -msse2 -msse3 -mcmodel=large
TARGET = ./all

all: LSD BSM SDALT Dijkstra
BSM: Regex2MinDFA.h BSM.cpp
	$(CXX) $(CFLAGS) -o BSM Regex2MinDFA.h BSM.cpp

LSD: LSD.cpp
	$(CXX) $(CFLAGS) -o LSD LSD.cpp
	
SDALT: Regex2MinDFA.h SDALT.cpp
	$(CXX) $(CFLAGS) -o SDALT Regex2MinDFA.h SDALT.cpp
	
Dijkstra: Regex2MinDFA.h Dijkstra.cpp
	$(CXX) $(CFLAGS) -o Dijkstra Regex2MinDFA.h Dijkstra.cpp

.PHONY: clean
clean:
		-@rm *.o *.gcno *~ 2> /dev/null || true
		-@rm SOR shortestPath SRH Statistic 2> /dev/null || true
