using namespace std;
#include <iostream>

//To execute: g++  main.cpp -o main && ./main

//This code refers to the work "Deciding Local Unitary Equivalence of Graph States in Quasi-Polynomial Time" which is free to access at https://arxiv.org/pdf/2502.06566
//Notably, this code relies on the definitions of 2-local complementation and 2-incidence from https://arxiv.org/pdf/2409.20183


////////////////////////////////////////// Auxiliary functions //////////////////////////////////////////

int binom(const int n, const int k);
//binomial coefficient
//requires k<=n
void iterate_word_same_weight(bool* word); 
//word is an array composed of 0's and 1's
//the function output the next word  having the same weight i.e. the same number of 1's
//The order is related to the number given by the base 2 representation
//The behavior is undefined when applying the function to a word with only 1's
bool is_contained(const bool* word1, const bool* word2, const int size);
//word1 and word2 are arrays composed of 0's and 1's
//is_contained() returns true if and only if for each position where word1 contains a 1, word2 contains a 1 as well
void print_array(const bool* array, const int size);
//prints an array composed of 0's and 1's
int weight_array(const bool* array, const int size);
//outputs the number of 1's in the array
int rankF2(bool** matrix, int nb_rows, int nb_columns);
//outputs the rank in the field F2 of a matrix composed of 0's and 1's
//essentially a Gaussian elimination

////////////////////////////////////////// End of auxiliary functions //////////////////////////////////////////



int main(int argc, const char* argv[]){





  ////////////////////////////////////////// Case 1: V minus S is of size 5 //////////////////////////////////////////

  {
  
  cout << endl;
  cout << "Case 1: V \\ S is of size 5" << endl << endl;
  cout << "Testing every 2**5=64 possible configuration of S :" << endl;

  //////////////// Definition of possible_vertices_of_S ////////////////

  //possible_vertices_of_S is an array containing every 26 vertex that may be in S
  //S can only contain vertices of degree at least 2, the the size of possible_vertices_of_S is binom(5,2)+binom(5,3)+binom(5,4)+binom(5,5)=10+10+5+1=26
  //A vertex is defined by its neighborhood (in V\S) i.e. a array composed of 0's and 1's of size 5
  //A set S is encoded as a array of 0's and 1's of size 26, where S[i]=1 if and only if S contains the vertex of neighbourhood possible_vertices_of_S[i]

  //possible_vertices_of_S is an array of arrays of size 26 * 5
  bool** possible_vertices_of_S = new bool*[26];
  for (int i=0; i<26; i++){
    possible_vertices_of_S[i] = new bool[5];
  }

  int sum_binom = 0;
  for (int degree_vertex=2; degree_vertex<=5; degree_vertex++){
    //The first vertex of degree 2 has neighbourhood [1,1,0,0,0]
    //The first vertex of degree 2 has neighbourhood [1,1,1,0,0], etc.
    bool neighbourhood_vertex[5] = {0};
    for (int k=0; k<degree_vertex; k++){
      neighbourhood_vertex[k]=1;
    }
    for (int k=degree_vertex; k<5; k++){
      neighbourhood_vertex[k]=0;
    }
    
    int number_vertices_degree = binom(5,degree_vertex); //number of vertices of degree degree_vertex

    for (int i=0; i<number_vertices_degree; i++){
      for (int j=0; j<5; j++){
        possible_vertices_of_S[sum_binom+i][j]=neighbourhood_vertex[j];          
      }
      if (i<number_vertices_degree-1) iterate_word_same_weight(neighbourhood_vertex);
    }

    sum_binom = sum_binom + number_vertices_degree;
  }

  //////////////// Definition of edges_of_V_minus_S ////////////////

  //edges_of_V_minus_S is an array containing every binom(5,2)=10 pairs of vertices of V\S
  //A pair of vertices is defined as a array composed of 0's and 1's of size 5 where the 1's correspond to the two vertices

  bool** edges_of_V_minus_S = new bool*[10]; 
  for (int i=0; i<10; i++){
    edges_of_V_minus_S[i] = new bool[5];
  }
  bool edge[5] = {1,1,0,0,0};
  for (int i=0; i<10; i++){
    for (int j=0; j<5; j++){
      edges_of_V_minus_S[i][j] = edge[j];
    }    
    if (i<9) iterate_word_same_weight(edge);
  }

  //////////////// Proof that a 2-local complementation over any 2-incident S leaves the graph invariant ////////////////  

  bool there_exist_S_having_effect_on_graph = false; 
  //there_exist_S_having_effect_on_graph will be set to true if for some S, a 2-local complementation over S toggles at least one edge in V\S
  //(This will not happen)

  //A 2-incident set S is uniquely determined by its vertices of degree at least 4
  //Thus, we generate every 2-incident set S by generating every combination of vertices of degree at least 4
  //S may contain binom(5,4)+binom(5,5)=6 different vertices of degree at least 4
  for (int number_vertices_of_degree_at_least_4=0; number_vertices_of_degree_at_least_4<=6; number_vertices_of_degree_at_least_4++){

    bool vertices_of_degree_at_least_4[6] = {0};
    for (int k=0; k<number_vertices_of_degree_at_least_4; k++){
      vertices_of_degree_at_least_4[k]=1;
    }
    for (int k=number_vertices_of_degree_at_least_4; k<5; k++){
      vertices_of_degree_at_least_4[k]=0;
    }

    int number_S = binom(6, number_vertices_of_degree_at_least_4); //number of possible S with number_vertices_of_degree_at_least_4 vertices of degree at least 4

    //We generate every 2-incident set S having exactly number_vertices_of_degree_at_least_4 vertices of degree at least 4
    for (int _=0; _<number_S ; _++){

      //The first 20 digits of S correspond to the vertices of degree at most 3
      //The last 6 digits of S correspond to the vertices of degree at least 4
      //First, we fix the vertices of S of degree at least 4
      bool S[26] = {0};
      for (int j=0; j<6; j++){
        S[20+j]=vertices_of_degree_at_least_4[j]; 
      }
      
      //Second, we complete S by adding vertices of degree at most 3 following the definition of 2-incidence
      for (int j=19; j>=0; j--){
        bool value = 0;
        for (int l = j+1; l<26; l++){
          value = value^( S[l] && is_contained(possible_vertices_of_S[j], possible_vertices_of_S[l], 5) );
        }  
        if (value) S[j] = 1;          
      }

      //edges_toggled_by_S described which edges in V\S are toggled by a 2-local complementation over S
      bool edges_toggled_by_S[10] = {0}; 
      for (int index_edge=0; index_edge<10; index_edge++){
        int count_common_neighbors = 0;
        for (int j = 0; j < 26; j++){
          if (S[j] && is_contained(edges_of_V_minus_S[index_edge], possible_vertices_of_S[j], 5)) count_common_neighbors++;
        }
        if (count_common_neighbors%4==1 || count_common_neighbors%4==3) cout << "error: S is not 2-incident";
        else if (count_common_neighbors%4==0) edges_toggled_by_S[index_edge]=0;
        else edges_toggled_by_S[index_edge]=1; //count_common_neighbors%4==2
      }

      //S_has_effect_on_graph becomes true if edges_toggled_by_S is not all 0's
      bool S_has_effect_on_graph = false;
      for (int j=0; j<10; j++){
        if (edges_toggled_by_S[j]){
          S_has_effect_on_graph=true;
        }
      }
      if (S_has_effect_on_graph) there_exist_S_having_effect_on_graph = true;

      if (_<number_S-1) iterate_word_same_weight(vertices_of_degree_at_least_4);
    }
  }
  cout << "64 / 64" << endl;
  if (there_exist_S_having_effect_on_graph)
    cout << "There exists a 2-incident set over which  a 2-local complementation does not leave the graph invariant." << endl;
  else cout << "For every 2-incident set S, a 2-local complementation over S leaves the graph invariant." << endl;

  cout << endl << endl;

  //////////////// free memory ////////////////
  for (int i=0; i<26; i++){
    delete[] possible_vertices_of_S[i];
  }
  delete[] possible_vertices_of_S;
  for (int i=0; i<10; i++){
    delete[] edges_of_V_minus_S[i];
  }
  delete[] edges_of_V_minus_S;
  //////////////////////////////////////////////
  }






  ////////////////////////////////////////// Case 2: V minus S is of size 6 //////////////////////////////////////////

  {

  cout << "Case 2: V \\ S is of size 6" << endl << endl;
  cout << "Testing every 2**22=4194304 possible configuration of S :" << endl;

  //////////////// Definition of possible_vertices_of_S ////////////////

  //possible_vertices_of_S is an array containing every 26 vertex that may be in S
  //S can only contain vertices of degree at least 2, the the size of possible_vertices_of_S is binom(6,2)+binom(6,3)+binom(6,4)+binom(6,5)+binom(6,6)=15+20+15+6+1=57
  //A vertex is defined by its neighborhood (in V\S) i.e. a array composed of 0's and 1's of size 6
  //A set S is encoded as a array of 0's and 1's of size 57, where S[i]=1 if and only if S contains the vertex of neighbourhood possible_vertices_of_S[i]

  //possible_vertices_of_S is an array of arrays of size 57 * 6
  bool** possible_vertices_of_S = new bool*[57]; 
  for (int i=0; i<57; i++){
    possible_vertices_of_S[i] = new bool[6];
  }

  int sum_binom = 0;
  for (int degree_vertex=2; degree_vertex<=6; degree_vertex++){
    //The first vertex of degree 2 has neighbourhood [1,1,0,0,0,0]
    //The first vertex of degree 2 has neighbourhood [1,1,1,0,0,0], etc.
    bool neighbourhood_vertex[6] = {0};
    for (int k=0; k<degree_vertex; k++){
      neighbourhood_vertex[k]=1;
    }
    for (int k=degree_vertex; k<6; k++){
      neighbourhood_vertex[k]=0;
    }
    
    int number_vertices_degree = binom(6,degree_vertex); //number of vertices of degree degree_vertex

    for (int i=0; i<number_vertices_degree; i++){
      for (int j=0; j<6; j++){
        possible_vertices_of_S[sum_binom+i][j]=neighbourhood_vertex[j];          
      }
      if (i<number_vertices_degree-1) iterate_word_same_weight(neighbourhood_vertex);
    }

    sum_binom = sum_binom + number_vertices_degree;
  }

  //////////////// Definition of edges_of_V_minus_S ////////////////

  //edges_of_V_minus_S is an array containing every binom(6,2)=15 pairs of vertices of V\S
  //A pair of vertices is defined as a array composed of 0's and 1's of size 5 where the 1's correspond to the two vertices

  bool** edges_of_V_minus_S = new bool*[15];
  for (int i=0; i<15; i++){
    edges_of_V_minus_S[i] = new bool[6];
  }
  bool edge[6] = {1,1,0,0,0,0};
  for (int i=0; i<15; i++){
    for (int j=0; j<6; j++){
      edges_of_V_minus_S[i][j] = edge[j];
    }    
    if (i<14) iterate_word_same_weight(edge);
  }

  //////////////// Definition of vertices_having_bigger_neighbourhood ////////////////

  //For the case V \ S of size 6, the number of graphs to test is way bigger (about 4 millions)
  //So we implement a more efficient data structure that stores the informations about which possible vertices of S have a bigger neighbourhood (by inclusion)
  //This will be useful to construct every possible 2-incident S
  //A vertex is encoded as a number i between 0 and 56, its neighbourhood is given by possible_vertices_of_S[i]

  int number_vertices_having_bigger_neighbourhood[57] = {0};
  int** vertices_having_bigger_neighbourhood = new int*[57];
  for (int i=0; i<57; i++){

    //First, for each vertex, we count the number of vertices having a bigger neighbourhood
    int count_vertices_having_bigger_neighbourhood = 0;
    for (int j=i+1; j<57; j++){
      if (is_contained(possible_vertices_of_S[i], possible_vertices_of_S[j], 6)) count_vertices_having_bigger_neighbourhood++;    
    }
    number_vertices_having_bigger_neighbourhood[i] = count_vertices_having_bigger_neighbourhood;

    //Second, for each vertex, we create the list of vertices having a bigger neighbourhood
    vertices_having_bigger_neighbourhood[i] = new int[count_vertices_having_bigger_neighbourhood];
    count_vertices_having_bigger_neighbourhood = 0;
    for (int j=i+1; j<57; j++){
      if (is_contained(possible_vertices_of_S[i], possible_vertices_of_S[j], 6)){
        vertices_having_bigger_neighbourhood[i][count_vertices_having_bigger_neighbourhood]=j;
        count_vertices_having_bigger_neighbourhood++; 
      }   
    }   

  }

  //////////////// Proof that a 2-local complementation over any 2-incident S of size at most 16 leaves the graph invariant ////////////////  
  //////////////// and that a 2-local complementation over any 2-incident S of size at most 20 can be implemented by local complementation //////////////// 

  bool there_exist_S_of_size_at_most_16_having_effect_on_graph = false;
  //there_exist_S_of_size_at_most_16_having_effect_on_graph will be set to true if for some S of size at most 16, a 2-local complementation over S toggles at least one edge in V\S
  //(This will not happen)
  bool there_exist_S_of_size_at_most_20_having_effect_on_graph_that_cannot_be_implemented_by_local_complementation = false;
  //there_exist_S_of_size_at_most_20_having_effect_on_graph_that_cannot_be_implemented_by_local_complementation will be set to true if for some S of size at most 20,
  //a 2-local complementation over S cannot be implemented by local complementations on vertices of S
  //(This will not happen)

  int count_S = 0;
  cout << count_S << " / 4194304" << flush;

  //A 2-incident set S is uniquely determined by its vertices of degree at least 4
  //Thus, we generate every 2-incident set S by generating every combination of vertices of degree at least 4
  //S may contain binom(6,4)+binom(6,5)+binom(6,6)=15+6+1=22 different vertices of degree at least 4
  for (int number_vertices_of_degree_at_least_4=0; number_vertices_of_degree_at_least_4<=22; number_vertices_of_degree_at_least_4++){ 

    bool vertices_of_degree_at_least_4[22] = {0};
    for (int k=0; k<number_vertices_of_degree_at_least_4; k++){
      vertices_of_degree_at_least_4[k]=1;
    }
    for (int k=number_vertices_of_degree_at_least_4; k<6; k++){
      vertices_of_degree_at_least_4[k]=0;
    }

    int number_S = binom(22, number_vertices_of_degree_at_least_4); //number of possible S with number_vertices_of_degree_at_least_4 vertices of degree at least 4

    //We generate every 2-incident set S having exactly number_vertices_of_degree_at_least_4 vertices of degree at least 4
    for (int _=0; _<number_S ; _++){

      //Keeping track of the progress and printing it 
      count_S++;
      if (count_S%10000==0 or count_S==4194304){
        for (int __=0; __< 17; __++){
				  cout << "\b";
			  }
        cout << count_S << " / 4194304" << flush;
      }

      //The first 35 digits of S correspond to the vertices of degree at most 3
      //The last 22 digits of S correspond to the vertices of degree at least 4
      //First, we fix the vertices of S of degree at least 4
      bool S[57] = {0};
      for (int j=0; j<22; j++){
        S[35+j]=vertices_of_degree_at_least_4[j];
      }

      //Second, we complete S by adding vertices of degree at most 3 following the definition of 2-incidence
      for (int i=34; i>=0; i--){
        bool value = 0;
        for (int j = 0; j<number_vertices_having_bigger_neighbourhood[i]; j++){
          value = value^S[vertices_having_bigger_neighbourhood[i][j]];
          //The computation of vertices_having_bigger_neighbourhood beforehand allows us not to call is_contained() each time (this saves a lot of time)
        }  
        if (value) S[i] = 1;          
      }

      int weight_S = weight_array(S,57); //weight_S is the number of vertices in S

      if (weight_S < 21){ //We only study S when it has at most 20 vertices 

        //edges_toggled_by_S described which edges in V\S are toggled by a 2-local complementation over S
        bool edges_toggled_by_S[15] = {0}; 
        for (int index_edge=0; index_edge<15; index_edge++){
          int count_common_neighbors = 0;
          for (int i = 0; i < 57; i++){
            if (S[i] && is_contained(edges_of_V_minus_S[index_edge], possible_vertices_of_S[i], 6)) count_common_neighbors++;
          }
          if (count_common_neighbors%4==1 || count_common_neighbors%4==3) cout << "error: S is not 2-incident";
          else if (count_common_neighbors%4==0) edges_toggled_by_S[index_edge]=0;
          else edges_toggled_by_S[index_edge]=1; //count_common_neighbors%4==2
        }

        //S_has_effect_on_graph becomes true if edges_toggled_by_S is not all 0's
        bool S_has_effect_on_graph = false;
        for (int i=0; i<15; i++){
          if (edges_toggled_by_S[i]){
            S_has_effect_on_graph=true;
          }
        }

        // Here we prove that is S contains at most 16 vertices, then a 2-local complementation over S has no effect on the graph.
        if (weight_S < 17 && S_has_effect_on_graph){      
          cout<< "Found an S of size at most 16 over which a 2-local complementation has an effect on the graph." << endl;
          there_exist_S_of_size_at_most_16_having_effect_on_graph = true;
        }

        // Here we prove that is S contains at most 20 vertices, then a 2-local complementation over S can be implemented by local complementations
        else if (S_has_effect_on_graph){

          //edges_toggled_by_local_complementations is an array of arrays of size weight_S*15
          //It reads as a generating set of the edges in V\S that can be toggled by local complementations over vertices of S
          //Each row of edges_toggled_by_local_complementations is the set of edges toggled by the corresponding vertex
          bool** edges_toggled_by_local_complementations = new bool*[weight_S]; 
          int vertex_of_S = 0;
          while (S[vertex_of_S]==0) vertex_of_S++;
          for (int i=0; i<weight_S; i++){
            edges_toggled_by_local_complementations[i] = new bool[15];          

            for (int j = 0; j < 15; j++){
              if (is_contained(edges_of_V_minus_S[j], possible_vertices_of_S[vertex_of_S], 6)){
                edges_toggled_by_local_complementations[i][j]=1;
              }
              else{
                edges_toggled_by_local_complementations[i][j]=0;
              }
            }
            vertex_of_S++;
            while (S[vertex_of_S]==0) vertex_of_S++;     
          }  
          
          //edges_toggled_by_local_complementations_and_2_local_complementation is an array of arrays of size (weight_S+1)*15
          //It reads as a generating set of the edges in V\S that can be toggled by local complementations over vertices of S AND a 2-local complementation over S
          //It is a copy of edges_toggled_by_local_complementations where we append edges_toggled_by_S as the last row
          bool** edges_toggled_by_local_complementations_and_2_local_complementation = new bool*[weight_S+1];  
          for (int i=0; i<weight_S; i++){
            edges_toggled_by_local_complementations_and_2_local_complementation[i] = new bool[15];
            for (int j=0; j<15; j++){
              edges_toggled_by_local_complementations_and_2_local_complementation[i][j] = edges_toggled_by_local_complementations[i][j];
            }
          } 
          edges_toggled_by_local_complementations_and_2_local_complementation[weight_S] = new bool[15];
          for (int j=0; j<15; j++){
            edges_toggled_by_local_complementations_and_2_local_complementation[weight_S][j] = edges_toggled_by_S[j];
          }

          //To know whether 2-local complementation over S can be implemented by local complementation, we compare the ranks in F2 of
          //edges_toggled_by_local_complementations and edges_toggled_by_local_complementations_and_2_local_complementation
          //If the rank is the same, then adding edges_toggled_by_S to edges_toggled_by_local_complementations does not increase the rank,
          //hence the edges toggled by a 2-local complementation over S can be toggled with only local complementations.
          if (rankF2(edges_toggled_by_local_complementations,weight_S,15)<rankF2(edges_toggled_by_local_complementations_and_2_local_complementation,weight_S+1,15)){
            cout << "The local complementations cannot implement a 2-local complementation over S:" << endl;
            print_array(S,57);
            cout << "which is of size " << weight_array(S,57) << " and over which a 2-local complementation toggles the edges " << endl;
            print_array(edges_toggled_by_S,15);
            cout << endl;
            there_exist_S_of_size_at_most_20_having_effect_on_graph_that_cannot_be_implemented_by_local_complementation = true;
          }

          //////////////// free memory ////////////////
          for (int i=0; i<weight_S; i++){
            delete[] edges_toggled_by_local_complementations[i];
          }
          delete[] edges_toggled_by_local_complementations;
          for (int i=0; i<weight_S+1; i++){
            delete[] edges_toggled_by_local_complementations_and_2_local_complementation[i];
          }
          delete[] edges_toggled_by_local_complementations_and_2_local_complementation;      
          //////////////////////////////////////////////

        }
      }
      if (_<number_S-1) iterate_word_same_weight(vertices_of_degree_at_least_4);
    }      
    
  }
  
  cout << endl;
  if (there_exist_S_of_size_at_most_16_having_effect_on_graph)
    cout << "There exists a 2-incident set S of size at most 16 over which a 2-local complementation leaves the graph invariant." << endl;
  else cout << "For any 2-incident set S of size at most 16, a 2-local complementation over S leaves the graph invariant." << endl;

  if (there_exist_S_of_size_at_most_20_having_effect_on_graph_that_cannot_be_implemented_by_local_complementation) 
    cout << "There exists a 2-incident set S of size at most 20 over which a 2-local complementation cannot be implemented by local complementations." << endl;
  else cout << "For any 2-incident set S of size at most 20, a 2-local complementation over S can be implemented by local complementations." << endl;
  cout << endl;


  //////////// free memory ////////////
  for (int i=0; i<57; i++){
    delete[] possible_vertices_of_S[i];
  }
  delete[] possible_vertices_of_S;
  for (int i=0; i<15; i++){
    delete[] edges_of_V_minus_S[i];
  }
  delete[] edges_of_V_minus_S;
  /////////////////////////////////////

  }  

}

////////////////////////////////////////// Definition of auxiliary functions //////////////////////////////////////////

int binom(int n, int k){
    if (n<k){
        std::cout << "error binomial coefficient" << std::endl;
        return -1;
    }
    if (n==k || k==0) return 1;
    if (k==1) return n;
    else{
        return binom(n-1, k) + binom(n-1, k-1);
    }
}

void iterate_word_same_weight(bool* array){
    int i = 0;
    while (array[i]==0) i++;
    int j = i;
    while (array[j]==1) j++;
    array[j]=1;
    array[i]=0;

    for(int k = j-1; k>i; k--){
        array[k]=0;
    }
    for(int k = j-i-2; k>=0; k--){
        array[k]=1;
    }
}

bool is_contained(const bool* word1, const bool* word2, const int size){
  for (int i = 0; i<size; i++){
    if (word1[i]==1 && word2[i]==0){
      return false;
    }
  }
  return true;
}

void print_array(const bool* array, const int size){
    if (array==NULL) std::cout << "empty array" << std::endl;
    else{
        for (int i = 0; i < size; i++) {
        std::cout << array[i] << " ";
    }
    std::cout << std::endl;
    }
}

int weight_array(const bool* array, const int size){
  int count = 0;
  for (int i = 0; i< size; i++){
    if (array[i]) count++;
  }
  return count;
}

int rankF2(bool** matrix, int nb_rows, int nb_columns){
  int rank = 0;
  
  for (int col =0; col < nb_columns && rank < nb_rows; col++){

    int pivot = rank;
    //finding the pivot
    while (pivot < nb_rows && matrix[pivot][col]==0){
      pivot++;
    }

    if (pivot==nb_rows) continue;

    //swapping the pivot column
    for (int j=0; j<nb_columns; j++){
      swap(matrix[rank][j], matrix[pivot][j]);
    }

    //elimination
    for (int i= rank +1; i < nb_rows; i++){
      if (matrix[i][col] == 1){
        for (int j = col; j < nb_columns; j++){
          matrix[i][j] ^= matrix[rank][j];
        }
      }
    }
    rank++;
  }
  return rank;
}