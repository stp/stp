import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.io.*;

/* Randomly generates problem instances that contain nested array operations */

// Both Indexes and values have the same bitwidth, potentially missing some errors.

// Doesn't generate extensional problems!

public class ArrayGenerator
{
    public static List<String> bits = new ArrayList<String>();
    public static List<String> arrays = new ArrayList<String>();
    static Random r = new Random();

    static int MAX_DEPTH;
    static int numberOfInstances = 500;

    public static void main(String[] args) throws IOException
    {
	bits.add("b1");
	bits.add("b2");
	bits.add("b3"); // Some case statements depend on there being 3 bitvectors.

	arrays.add("a1");
	arrays.add("a2");
	arrays.add("a3");


	for (int i=0; i < numberOfInstances; i++)
	{
		// When we get to the nesting depth, start to return leaf nodes (like symbols).
		MAX_DEPTH = r.nextInt(15) +1;

		randomGenerate("f"+i+".smt");
    
	}
}

    static void randomGenerate(String fileName) throws IOException
    {
	StringBuilder output = new StringBuilder();
	output.append("(\n");
	output.append("benchmark t.smt\n");
	output.append(":source {automatically generated}\n");
	output.append(":status unknown\n");
	output.append(":logic QF_AUFBV\n");

	for (String s : bits)
	{
	    output.append(":extrafuns (( " + s + " BitVec[4]))\n");
	}

	for (String s : arrays)
	{
	    output.append(":extrafuns (( " + s + " Array[4:4]))\n");
	}

	int top = r.nextInt(10);
	for (int i = 0; i < top+1; i++)
	    output.append(":assumption " + generateProp(0) + "\n");

	output.append(":formula true \n )\n");
	
	FileWriter fstream = new FileWriter(fileName);
	  BufferedWriter out = new BufferedWriter(fstream);
	  out.write(output.toString());
	  out.close();

    }

    // Arrays are either array symbols, ites, or stores.
    static String generateArray(int depth)
    {
	int next =r.nextInt(5);
	if (depth > MAX_DEPTH)
	    next  = next %3;

	depth++;
	
	switch (next)
	{
	case 0:
	case 1:
	case 2:
	    return arrays.get(next);
	case 3:
	    return "(ite " + generateProp(depth) + " " + generateArray(depth) + " " + generateArray(depth) + " )";
	case 4:
	    return "(store " + generateArray(depth) + " " + generateBit(depth) + " " + generateBit(depth) + " )";
	}

	throw new RuntimeException("Never here");
    }

    // BitVectors.
    static String generateBit(int depth)
    {

	int next =r.nextInt(6);
	if (depth > MAX_DEPTH)
	    next  = next %3;
	
	depth++;
	
	switch (next)
	{
	case 0:
	case 1:
	case 2:
	    return bits.get(next);

	case 3:
	    return "(select " + generateArray(depth) + " " + generateBit(depth) + " )";

	case 4:
	    return "(ite " + generateProp(depth) + " " + generateBit(depth) + " " + generateBit(depth) + " )";

	case 5:
	    return "(bvadd " + generateBit(depth) + " " + generateBit(depth) + " )";

	}

	throw new RuntimeException("Never here");

    }

    static String generateProp(int depth)
    {
	int next =r.nextInt(6);
	if (depth > MAX_DEPTH)
	    next  = next %2;
	
	depth++;
	
	switch (next)
	{
	case 0: 
	    return "true";
	case 1:
	    return "(= " + generateBit(depth) + " " + generateBit(depth) + " )";
	case 2: 
	    return "(or " + generateProp(depth) + " " + generateProp(depth) + " )";
	case 3: 
	    return "(bvslt " + generateBit(depth) + " " + generateBit(depth) + " )";
	case 4: 
	    return "(iff " + generateProp(depth) + " " + generateProp(depth) + " )";
	case 5: 
	    return "(ite " + generateProp(depth) + " " + generateProp(depth) + " " + generateProp(depth) + " )";
	}
	throw new RuntimeException("Never here");
	}

}
