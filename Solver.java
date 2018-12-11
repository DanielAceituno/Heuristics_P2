import java.io.BufferedReader;
import java.io.FileReader;
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

    Store store = new Store();
		SatWrapper satWrapper = new SatWrapper();
		store.impose(satWrapper);

    String map="";
    String line;
    FileReader reader = new FileReader(args[0]);
    BufferedReader buffer = new BufferedReader(reader);
    while((line=buffer.readLine()) != null){
      map+=line+",";
    }
    buffer.close();

    String [] elementsMap=map.split(",");

    int numRows=elementsMap.length;
    int numCol=elementsMap[0].length();
    System.out.println("Number of rows:"+numRows);
    System.out.println("Number of columns:"+numCol);

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

    //COUNTING ALL THE TILES THAT ARE NOT FREE:
    int filledTiles=0;
    for(int z=0;z<numCol*numRows;z++){
      if(!allRows[z].equals(" ")){
        filledTiles++;
      }
    }

    /*for(int u=0;u<allRows.length;u++){ PARA PRINTEAR ALLROWS
      System.out.print(allRows[u]);
    } */

    /*for(int o=0;o<numRows;o++){ PARA PRINTEAR MAPCONTENT
      for(int p=0;p<numCol;p++){
        System.out.print(mapContent[o][p]);
      }
    } */

    //Proceeding to the phase of creating variables for the SAT problem.

    //SI NO ENTIENDES BIEN ESTA PARTE ECHA UN OJO AL SEGURIDAD.JAVA, ES EL MISMO PROCESO.
    BooleanVar [] allVariables=new BooleanVar[numRows*numCol+filledTiles];

    int [] literals=new int [numRows*numCol+filledTiles];

    for(int i=0;i<numRows*numCol;i++){
      allVariables[i]=new BooleanVar(store, "Al is placed in position "+i+" of the map.");
      satWrapper.register(allVariables[i]);
      literals [i] = satWrapper.cpVarToBoolVar(allVariables[i], 1, true);
    }

    for(int j=0;j<filledTiles;j++){
      allVariables[numRows*numCol+j]=new BooleanVar(store, "There is an obstacle (with ID "+j+")");
      satWrapper.register(allVariables[numCol*numRows+j]);
      literals [numCol*numRows+j] = satWrapper.cpVarToBoolVar(allVariables[numCol*numRows+j], 1, true);
    }

    addAltoMap(satWrapper, literals, allRows); //Call to function to place Al.

    Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
  SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
             new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
  Boolean result = search.labeling(store, select);

  System.out.println("Number of cells in the map:"+numCol*numRows);
  }



  public static void addAltoMap(SatWrapper satWrapper, int literals[], String allRows[]){
    int k=0;
    for(int i=0;i<allRows.length;i++){ //This part will make sure that only one or no Al can exist at the same time.
      for(int j=0;j<allRows.length;j++){ //(-a1 v -a2)^(-a1 v -a3)...
        if(i!=j){
          IntVec clause = new IntVec(satWrapper.pool);
          int auxVal1=literals[i];
          int auxVal2=literals[j];
      		clause.add(-auxVal1);
      		clause.add(-auxVal2);
      		satWrapper.addModelClause(clause.toArray());
        }
      }
    }
    IntVec clause2 = new IntVec(satWrapper.pool); //This part will force that there is at least one tile containing Al.
    for(int l=0;l<allRows.length;l++){ //(a1 v a2 v a3 v a4...)
      int aux=literals[l];
      clause2.add(aux);
    }
    satWrapper.addModelClause(clause2.toArray());

    //Adding clauses so that Al cannot be placed in any kind of obstacle.
    int countingFilled=0;
    for(int w=0;w<allRows.length;w++){
      if(!allRows[w].equals(" ")){
        IntVec clause3 = new IntVec(satWrapper.pool);
        int auxVal1=literals[allRows.length+countingFilled];
        int auxVal2=literals[w];
        clause3.add(-auxVal1);
        clause3.add(-auxVal2);
        satWrapper.addModelClause(clause3.toArray());

        //This will force the existance of an obstacle to be true if there is any:
        IntVec clause4 = new IntVec(satWrapper.pool);
        clause4.add(literals[allRows.length+countingFilled]);
        satWrapper.addModelClause(clause4.toArray());

        countingFilled++;
      }
    }
  }

}
