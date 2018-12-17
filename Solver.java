import java.io.BufferedReader;
import java.io.FileReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.File;
import java.io.IOException;
import java.io.FileNotFoundException;
//Library imports from JaCop:
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/*To compile and run the program:
  javac -classpath .:jacop-4.3.0.jar Solver.java
  java -classpath .:jacop-4.3.0.jar Solver*/

public class Solver{

  public static void main(String args[]) throws Exception{

    //Creating the store and SAT wrapper for JaCop:
    Store store = new Store();
		SatWrapper satWrapper = new SatWrapper();
		store.impose(satWrapper);

    //Storing the elements of the input file:
    String map=""; //This var will contain all the elements pf the map separated by a ",".
    String line; //Will store the current line of the file for each iteration of the loop.
    FileReader reader = new FileReader(args[0]);
    BufferedReader buffer = new BufferedReader(reader);
    while((line=buffer.readLine()) != null){
      map+=line+",";
    }
    buffer.close();

    String [] elementsMap=map.split(",");

    //Variables storing the number of rows and columns (width and height) of the read maze.
    int numRows=elementsMap.length;
    int numCol=elementsMap[0].length();

    String [] rowContent; //Auxiliar variable for obtaining the data from elementsMap.

    String [][] mapContent=new String[numRows][numCol]; //Matrix containing all the data from the map.
    String [] allRows=new String[numRows*numCol]; //Array containing all the data from the map in 1 dimension.

    //Filling up the content of mapContent and allRows.
    for(int x=0;x<numRows;x++){
      rowContent=elementsMap[x].split("");
      for(int y=0;y<rowContent.length;y++){
        mapContent[x][y]=rowContent[y];
        allRows[(x*numCol+y)]=rowContent[y];
      }
    }

    //Proceeding to the phase of creating variables for the SAT problem.

    int numSnakes=Integer.parseInt(args[1]); //Number of desired snakes obtained from the second input.
    int numberOfParallelGrids=1+numSnakes; //Number of grids of boolean variables that will be created (Al + Snakes)

    //Containers for the SAT problem variables:
    BooleanVar [] allVariables=new BooleanVar[numberOfParallelGrids*numRows*numCol];
    int [] literals=new int [numberOfParallelGrids*numRows*numCol];

    //Initializing Al's placement boolean variables.
    for(int i=0;i<numRows*numCol;i++){
      allVariables[i]=new BooleanVar(store, "Al is placed in position "+i+" of the map.");
      satWrapper.register(allVariables[i]);
      literals [i] = satWrapper.cpVarToBoolVar(allVariables[i], 1, true);
    }

    //Call to function to place Al. Offset=0 is for Al.
    addElementToMap(satWrapper, literals, allRows, 0);

    //Initializing the Snakes's placement boolean variables.
    for(int s=0;s<numSnakes;s++){
      //This loop will initialize the variables for Snake "s":
      for(int k=0;k<numRows*numCol;k++){
        allVariables[k+((s+1)*numRows*numCol)]=new BooleanVar(store, "Snake"+(s+1)+" is placed in position "+k+" of the map.");
        satWrapper.register(allVariables[k+((s+1)*numRows*numCol)]);
        literals [k+((s+1)*numRows*numCol)] = satWrapper.cpVarToBoolVar(allVariables[k+((s+1)*numRows*numCol)], 1, true);
      }
      /*Calls to the functions for placing the Snakes, and the interaction between the Snakes and Al,
      In the following code (s+1)*numCol*numRows represents the offset for the variables of the current
      snake in the arrays allVariables and literals.*/
      addElementToMap(satWrapper, literals, allRows, (s+1)*numCol*numRows);
      snakesAndAl(satWrapper, literals, (s+1)*numCol*numRows, numRows, numCol);
    }

    //Loop for calling the function for interaction among snakes:
    for(int t=1;t<=numSnakes;t++){
      for(int u=1;u<=numSnakes;u++){
        if(t!=u){
          snakesAndSnakes(satWrapper, literals, t*numCol*numRows, u*numCol*numRows, numRows, numCol);
        }
      }
    }

    //Calling JaCop to solve the SAT instance:
    Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
    SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables, new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
    Boolean result = search.labeling(store, select);

    //Obtaining the results for the boolean variables.
    int checkIfValid=0; //This value will only stay equals to 0 if every boolean variable is 0, that is, the instance is not satisfiable.
    //Placing an "A" in the location of Al in the map.
    for(int n=0;n<numCol*numRows;n++){
      if(allVariables[n].dom().value()==1){
        allRows[n]="A";
        checkIfValid++;
      }
    }

    //Placing an "S" in the location of the Snakes in the map.
    for(int p=0;p<numSnakes;p++){
      for(int q=0;q<numCol*numRows;q++){
        if(allVariables[numRows*numCol+q+(p*numRows*numCol)].dom().value()==1){
          allRows[q]="S";
          checkIfValid++;
        }
      }
    }

    if(checkIfValid==0){
      System.out.println("This instance of the problem is not satisfiable.");
    }

    else{
      //For printing and writing into the file the result once finished.
      System.out.println("This instance is satisfiable. The obtained valid configuration is the following:");
      String nameOutput=args[0]+".output";
      File outFile=new File(nameOutput);
      outFile.createNewFile();
      FileWriter filewriter=new FileWriter(outFile);
      BufferedWriter bufWriter=new BufferedWriter(filewriter);

      int elemCounter=0;
      for(int o=0;o<allRows.length;o++){
        System.out.print(allRows[o]);
        bufWriter.write(allRows[o]);
        elemCounter++;
        if(elemCounter>=numCol){
          System.out.println("");
          bufWriter.newLine();
          elemCounter=0;
        }
      }
      System.out.println("The results have been written to the file: "+nameOutput);
      bufWriter.close();
    }
  }



  public static void addElementToMap(SatWrapper satWrapper, int literals[], String allRows[], int offset){
    int k=0;
    for(int i=0;i<allRows.length;i++){ //This part will make sure that only one or no Al or Snake can exist at the same time.
      for(int j=0;j<allRows.length;j++){ //(-a1 v -a2)^(-a1 v -a3)...
        if(i!=j){
          IntVec clause = new IntVec(satWrapper.pool);
      		clause.add(-literals[i+offset]);
      		clause.add(-literals[j+offset]);
      		satWrapper.addModelClause(clause.toArray());
        }
      }
    }
    IntVec clause2 = new IntVec(satWrapper.pool); //This part will force that there is at least one tile containing Al or a Snake.
    for(int l=0;l<allRows.length;l++){ //(a1 v a2 v a3 v a4...)
      clause2.add(literals[l+offset]);
    }
    satWrapper.addModelClause(clause2.toArray());

    //Adding clauses so that Al or Snake cannot be placed in any kind of obstacle.
    for(int w=0;w<allRows.length;w++){

      if(!allRows[w].equals(" ")){
        IntVec clause3 = new IntVec(satWrapper.pool);
        clause3.add(-literals[w+offset]);
        satWrapper.addModelClause(clause3.toArray());

      }
    }
  }

  public static void snakesAndAl(SatWrapper satWrapper, int literals[], int offset, int numRows, int numCol){
      for(int i=0;i<numRows;i++){
        for(int j=0;j<numCol;j++){
          //Part for not generating snakes in the same row as Al.
          for(int k=0;k<numCol;k++){
            IntVec clause = new IntVec(satWrapper.pool);
            clause.add(-literals[i*numCol+j]);
            clause.add(-literals[i*numCol+k+offset]);
            satWrapper.addModelClause(clause.toArray());
          }
          //Part for not generating snakes in the same column as Al.
          for(int l=0;l<numRows;l++){
            IntVec clause2 = new IntVec(satWrapper.pool);
            clause2.add(-literals[i*numCol+j]);
            clause2.add(-literals[l*numCol+j+offset]);
            satWrapper.addModelClause(clause2.toArray());
          }
        }
      }
  }

  public static void snakesAndSnakes(SatWrapper satWrapper, int literals[], int offset1, int offset2, int numRows, int numCol){

    for(int i=0;i<numRows;i++){
      for(int j=0;j<numCol;j++){
        //Part for not generating snakes in the same row as other Snakes.
        for(int k=0;k<numCol;k++){
          IntVec clause = new IntVec(satWrapper.pool);
          clause.add(-literals[i*numCol+j+offset1]);
          clause.add(-literals[i*numCol+k+offset2]);
          satWrapper.addModelClause(clause.toArray());
        }
      }
    }
  }

}
