package de.uka.ilkd.key.smt;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.lang.SMTFunction;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.Util;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Location;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;
/**
 * Represents a query directed to towards the z3 solver.
 * @author mihai
 *
 */
interface Query {

	public static final String SELECT_ID =  "select_";
	/**
	 * Stores the result from the z3 solver.
	 * @param s
	 */
	public void setResult(String s);	
	/**
	 * Returns the command that is to be handed over to the z3 solver.
	 * @return
	 */
	public String getQuery();
	/**
	 * Returns the stored result.
	 * @return
	 */
	public String getResult();

}

abstract class AbstractQuery implements Query{


	protected String result;	

	public AbstractQuery() {
		super();		
		this.result = null;
	}


	/**
	 * @return the result
	 */
	public String getResult() {
		return result;
	}
	/**
	 * @param result the result to set
	 */
	public void setResult(String result) {
		this.result = result;
	}

	protected String enclose(String arg) {
		return "( " + arg + " )";
	}

	protected String echo(String arg) {
		return "( echo \"" + arg + "\" )";
	}

	protected String getVal(String arg) {
		return "( get-value " + arg + " )";
	}


}




/**
 * Query for constant values.
 * @author mihai
 *
 */
class ConstantQuery extends AbstractQuery{	

	public ConstantQuery(String constantID) {
		super();
		this.constantID = constantID;
	}

	private String constantID;

	/**
	 * @return the constantID
	 */
	public String getConstantID() {
		return constantID;
	}

	@Override
	public String getQuery() {
		return getVal(enclose(constantID));
	}

	public void setResult(String s){
		s = s.trim();
		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace("|", "");
		String[] values = s.split(" ");
		result = values[1];		

	}
}
/**
 * Query for the value of a position of a sequence.
 * @author mihai
 *
 */
class SeqFieldQuery extends AbstractQuery{
	
	private Sequence seqID;

	private int index;
	private int intBound;



	public SeqFieldQuery(Sequence seq,  int index, int bound) {
		super();
		this.seqID = seq;
		
		this.index = index;
		
		intBound = bound;
	}





	public Sequence getSeq() {
		return seqID;
	}








	public int getIndex() {
		return index;
	}





	@Override
	public String getQuery() {
		String val = "(_ bv"+index+" " +intBound+")";
		

		String q = enclose(SMTObjTranslator.SEQ_GET + " "
				+ seqID.getName() +  " " + val);

		q = enclose(q);

		String result = getVal(q);
		//System.out.println(result);
		return result;
	}

	public void setResult(String s){

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace("  ", " ");
		s = s.replace("  ", " ");
		s = s.replace("|", "");
		s = s.trim();
		String[] parts = s.split(" ");		
		result = parts[5];


	}
}
/**
 * Query for the value of an array field of an object in a heap.
 * @author mihai
 *
 */
class ArrayFieldQuery extends AbstractQuery{

	// TODO Auto-generated method stub
	private String heapID;
	private String objectID;
	private int index;
	private int intBound;



	public ArrayFieldQuery(String heapID, String objectID, int index, int bound) {
		super();
		this.heapID = heapID;
		this.objectID = objectID;
		this.index = index;
		
		intBound = bound;
	}





	public String getHeapID() {
		return heapID;
	}





	public String getObjectID() {
		return objectID;
	}





	public int getIndex() {
		return index;
	}





	@Override
	public String getQuery() {
		String val = "(_ bv"+index+" " +intBound+")";
		String arr = enclose("arr "+val);

		String q = enclose(SELECT_ID + " "
				+ heapID + " " + objectID + " " + arr);

		q = enclose(q);

		String result = getVal(q);
		//System.out.println(result);
		return result;
	}

	public void setResult(String s){

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace("  ", " ");
		s = s.replace("  ", " ");
		s = s.replace("|", "");
		s = s.trim();
		String[] parts = s.split(" ");		
		result = parts[7];


	}



}

/**
 * Query for the value of a named field of an object in a heap.
 * @author mihai
 *
 */
class FieldQuery extends AbstractQuery{

	private String heapID;
	private String objectID;
	private String fieldID;


	public FieldQuery(String heapID, String objectID, String fieldID) {
		super();
		this.heapID = heapID;
		this.objectID = objectID;
		this.fieldID = fieldID;
		
		//System.out.println(getQuery());
		
	}


	public String getHeapID() {
		return heapID;
	}


	public String getObjectID() {
		return objectID;
	}


	public String getFieldID() {
		return fieldID;
	}


	@Override
	public String getQuery() {

		String q = enclose(SELECT_ID + " "
				+ heapID + " " + objectID + " " + fieldID);

		q = enclose(q);

		return getVal(q);
	}

	public void setResult(String s){

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace("  ", " ");
		s = s.replace("|", "");
		s = s.trim();
		String[] parts = s.split(" ");		
		result = parts[4];


	}

}
/**
 * Query for checking if a location is in a location set.
 * @author mihai
 *
 */
class LocSetQuery extends AbstractQuery{


	private String locSetID;
	private String objectID;
	private String fieldID;




	public LocSetQuery(String locSetID, String objectID, String fieldID) {
		super();
		this.locSetID = locSetID;
		this.objectID = objectID;
		this.fieldID = fieldID;
	}

	public String getLocSetID() {
		return locSetID;
	}

	public String getObjectID() {
		return objectID;
	}

	public String getFieldID() {
		return fieldID;
	}

	@Override
	public String getQuery() {		
		String q = enclose(SMTObjTranslator.ELEMENTOF + " " + objectID + " "
				+ fieldID + " " + locSetID);
		q = enclose(q);
		return getVal(q);
	}	

	public void setResult(String s){		

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace("elementOf", "");
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");

		result = parts[3];


	}



}
/**
 * Query for finding out the length of a sequence.
 * @author mihai
 *
 */
class SeqLengthQuery extends AbstractQuery{
	
	private String seqID;

	public String getSeqID() {
		return seqID;
	}


	public SeqLengthQuery(String objectID) {
		super();
		this.seqID = objectID;
	}

	@Override
	public String getQuery() {

		String q = enclose(SMTObjTranslator.SEQ_LEN+" "+seqID);
		q = enclose(q);
		return getVal(q);


	}

	public void setResult(String s){		

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace(SMTObjTranslator.SEQ_LEN, "");
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");
		String value = parts[1];
		int x;
		if(value.startsWith("#x")){
			value = value.replace("#x", "");
			x = Integer.parseInt(value, 16);
		}
		else{
			value = value.replace("#b", "");
			x = Integer.parseInt(value, 2);
		}

		value = Integer.toString(x);	

		result = value;


	}
	
}
/**
 * Query for finding out the length of an object.
 * @author mihai
 *
 */
class ObjectLengthQuery extends AbstractQuery{

	private String objectID;



	public String getObjectID() {
		return objectID;
	}


	public ObjectLengthQuery(String objectID) {
		super();
		this.objectID = objectID;
	}

	@Override
	public String getQuery() {

		String q = enclose(SMTObjTranslator.LENGTH+" "+objectID);
		q = enclose(q);
		return getVal(q);


	}

	public void setResult(String s){		

		s = s.replace("(", "");
		s = s.replace(")", "");
		s = s.replace(SMTObjTranslator.LENGTH, "");
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");
		String value = parts[1];
		int x;
		if(value.startsWith("#x")){
			value = value.replace("#x", "");
			x = Integer.parseInt(value, 16);
		}
		else{
			value = value.replace("#b", "");
			x = Integer.parseInt(value, 2);
		}

		value = Integer.toString(x);	

		result = value;


	}

}
/**
 * Query for finding out the value of a function(classinvariant or model field) for an object in a heap.
 * @author mihai
 *
 */
class FunValueQuery extends AbstractQuery{
	
	private String objectId;
	
	private String heapID;
	
	private String functionID;
	
	
	

	public FunValueQuery(String objectId, String heapID, String functionID) {
		super();
		this.objectId = objectId;
		this.heapID = heapID;
		this.functionID = functionID;
	}

	public String getObjectID() {
		return objectId;
	}

	public String getHeapID() {
		return heapID;
	}

	public String getFunctionID() {
		return functionID;
	}

	@Override
	public String getQuery() {
		String q = functionID + " " + heapID + " " + objectId;
		
		q = enclose(q);
		q = enclose(q);
		q = getVal(q);
		
		return q;
	}
	
	public void setResult(String s){
		s = s.replace("(", "");
		s = s.replace(")", "");
		
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");
		result = parts[3];
	}
	
}
/**
 * Query for finding out if an object is an exact instance of its sort.
 * @author mihai
 *
 */
class ExactInstanceQuery extends AbstractQuery{
	private String objectId;
	private Sort sort;
	
	
	
	
	public ExactInstanceQuery(String objectId, Sort sort) {
		super();
		this.objectId = objectId;
		this.sort = sort;
	}



	public String getObjectId() {
		return objectId;
	}



	public Sort getSort() {
		return sort;
	}



	@Override
	public String getQuery() {
		
		
		
		String typeof = Util.processName(SMTObjTranslator.getExactInstanceName(sort.name().toString()));
		
		String q = enclose(typeof+" "+objectId);
		q = enclose(q);
		q = getVal(q);
		
		
		
		return q;
		
		
	}
	
	public void setResult(String s){
		s = s.replace("(", "");
		s = s.replace(")", "");
		
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");
		result = parts[2];
	}
}
/**
 * Query for finding out if a given object is of a given sort.
 * @author mihai
 *
 */
class ObjectTypeQuery extends AbstractQuery{
	
	private String objectId;
	private Sort sort;
	
	
	
	
	public ObjectTypeQuery(String objectId, Sort sort) {
		super();
		this.objectId = objectId;
		this.sort = sort;
	}



	public String getObjectId() {
		return objectId;
	}



	public Sort getSort() {
		return sort;
	}



	@Override
	public String getQuery() {
		
		String typeof = Util.processName(SMTObjTranslator.getTypePredicateName(sort.name().toString()));
		
		String q = enclose(typeof+" "+objectId);
		q = enclose(q);
		return getVal(q);
	}
	
	public void setResult(String s){
		s = s.replace("(", "");
		s = s.replace(")", "");
		
		s = s.replace("|", "");
		s = s.replace("  ", " ");
		s = s.trim();		
		String[] parts = s.split(" ");
		result = parts[2];
	}
	
	
	
}





/**
 * Class for sending queries to the solver and extracting the relevant information regarding the model.
 * @author mihai
 *
 */
public class ModelExtractor implements PipeListener<SolverCommunication>{

	public static final int DEFAULT = 0;
	public static final int TYPES = 4;
	public static final int WORKING = 1;
	public static final int ARRAYFIELDS = 2;
	public static final int FINISHED = 3;
	public static final int SEQ = 5;

	private Model model;


	private int state;


	private List<SMTFunction> heaps;
	private List<SMTFunction> objects;
	private List<SMTFunction> fields;
	private List<SMTFunction> locsets;
	private List<SMTFunction> ints;
	private List<SMTFunction> bools;
	private List<SMTFunction> seqs;
	private Map<String,SMTSort> objFunctions;

	private ProblemTypeInformation types;
	private Map<String,Sort> objectSorts;

	private List<Query> queries;	
	private int currentQuery;
	private int intBound;



	public void addFunction(SMTFunction f){		
		if (f.getDomainSorts().size() == 0) {
			if (f.getImageSort().getId().equals(SMTObjTranslator.HEAP_SORT)) {
				heaps.add(f);
			} else if (f.getImageSort().getId().equals(SMTObjTranslator.FIELD_SORT)) {
				fields.add(f);
			} else if (f.getImageSort().getId().equals(SMTObjTranslator.LOCSET_SORT)) {
				locsets.add(f);
			} else if (f.getImageSort().getId().equals(SMTObjTranslator.OBJECT_SORT)) {
				objects.add(f);
			} else if (f.getImageSort().getId().equals(SMTObjTranslator.BINT_SORT)) {
				ints.add(f);
			}else if (f.getImageSort().getId().equals(SMTObjTranslator.SEQ_SORT)) {
				seqs.add(f);
			}
			else {
				bools.add(f);
			}
		}
		else if(f.getDomainSorts().size() == 2){
			
			SMTSort s1 = f.getDomainSorts().get(0);
			SMTSort s2 = f.getDomainSorts().get(1);
			
			if(s1.getId().equals(SMTObjTranslator.HEAP_SORT) 
					&& s2.getId().equals(SMTObjTranslator.OBJECT_SORT)){
				
				objFunctions.put(f.getId(), f.getImageSort());
				
				
				
			}
			
			
			
			
			
		}
	}



	public Model getModel() {
		return model;
	}
	
	private void generateTypeQueries(){
		queries = new LinkedList<Query>();
		currentQuery = 0;
		
		for(String objectID : getAllIDs((int) types.getSettings().getObjectBound())){
			
			
			for(Sort s : types.getJavaSorts()){
				
				
				
				Query q = new ObjectTypeQuery(objectID, s);
				queries.add(q);
				
				
			}
			
			
		}
		
		
		
	}



	private void generateBasicQueries(){
		queries = new LinkedList<Query>();
		currentQuery = 0;
		//generate constant queries

		List<SMTFunction> constants = new LinkedList<SMTFunction>();
		constants.addAll(objects);
		constants.addAll(locsets);
		constants.addAll(bools);
		constants.addAll(fields);
		constants.addAll(ints);
		constants.addAll(heaps);
		constants.addAll(seqs);

		for(SMTFunction f : constants){			
			String constantID = f.getId();			
			ConstantQuery q = new ConstantQuery(constantID);
			queries.add(q);			
		}

		//generate heap queries

		for(SMTFunction h : heaps){
			String heapID = h.getId();
			
			
			
			for(String objectID : getAllIDs((int) types.getSettings().getObjectBound())){
				
				//generate the obj inv query
				
				
				for(String fun : objFunctions.keySet()){
					
//					System.out.println("Query: "+fun);
					
					FunValueQuery iq = new FunValueQuery(objectID, heapID,fun);
					queries.add(iq);
				}
				
				
				
				
				//generate the named fields queries
				for(SMTFunction f : fields){
					String fieldID = f.getId();
					
					
					
					Sort s = objectSorts.get(objectID);
					Set<String> fields; 
					if(s == null){
						fields = types.getFieldsForSort("java.lang.Object");
					}
					else{
						
						fields = types.getFieldsForSort(s);
					}
					
					
					if(fields.contains(fieldID)){
						Query q = new FieldQuery(heapID, objectID, fieldID);
						queries.add(q);
					}
					
					
					


				}				
			}			
		}
		
		//generate exactInstance queries
		
		for(String objectID : getAllIDs((int) types.getSettings().getObjectBound())){
			
			if(objectID.equals("#o0"))
				continue;
			
			
			Sort s = objectSorts.get(objectID);
			if(s != null){
				ExactInstanceQuery eq = new ExactInstanceQuery(objectID, s);
				queries.add(eq);
			}
			
			
			
			
		}
		

		//generate locset Queries
		int locsetSize = (int) types.getSettings().getLocSetBound();
		for(String locSetID : getAllIDs(locsetSize)){
			
			for(String objectID : getAllIDs((int) types.getSettings().getObjectBound())){
												
				int fieldSize = (int) types.getSort(SMTObjTranslator.FIELD_SORT).getBitSize();
				int intBound = (int) types.getSort(SMTObjTranslator.BINT_SORT).getBound();				
				
				
				int i = 0;
				for(String fieldID : getAllIDs(fieldSize)){
					
					if(i++ >= intBound/2){
						break;
					}
					
					Query q = new LocSetQuery(locSetID, objectID, fieldID);
					queries.add(q);
				}
				
				for(SMTFunction f : fields){
					String fieldID = f.getId();
					Query q = new LocSetQuery(locSetID, objectID, fieldID);
					queries.add(q);
				}
				
			}
			
		}

		//generate Object length queries

		for(String objectID : getAllIDs((int) types.getSettings().getObjectBound())){
			

			Query q = new ObjectLengthQuery(objectID);
			queries.add(q);


		}
		
		//generate Seq len query
		
		for(String seqID  : getAllIDs((int) types.getSettings().getSeqBound())){
			
			Query q = new SeqLengthQuery(seqID);
			queries.add(q);
		}
		
	}
	
	private void generateArrayQueries(){
		queries = new LinkedList<Query>();
		currentQuery = 0;
		
		for(Heap h : model.getHeaps()){
			
			for(ObjectVal ov : h.getObjects()){
				
				if(ov.getSort() == null){
					//System.out.println(ov.getName()+" has no sort!");
					continue;
				}
				
				String sortName = ov.getSort().name().toString();
				
				if(!sortName.endsWith("[]")){
					continue;
				}
				
				
				
				
				for(int i = 0; i<ov.getLength();++i){
					
					Query q = new ArrayFieldQuery(h.getName(), ov.getName(), i,intBound);
					queries.add(q);
				}				
			}			
		}		
	}
	
	private void generateSeqQueries(){
		queries = new LinkedList<Query>();
		currentQuery = 0;
		
		for(Sequence s : model.getSequences()){
			
			for(int i = 0; i< s.getLength(); ++i){
				
				SeqFieldQuery q = new SeqFieldQuery(s, i, (int) types.getSettings().getIntBound());
				queries.add(q);
			}
			
			
		}
		
		
	}






	public int getIntBound() {
		return intBound;
	}



	public void setIntBound(int intBound) {
		this.intBound = intBound;
	}



	public ModelExtractor() {
		super();
		state = DEFAULT;
		currentQuery = -1;
		heaps =  new LinkedList<SMTFunction>();
		objects = new LinkedList<SMTFunction>();
		fields = new LinkedList<SMTFunction>();
		ints = new LinkedList<SMTFunction>();
		locsets = new LinkedList<SMTFunction>();
		bools = new LinkedList<SMTFunction>();
		objectSorts = new HashMap<String,Sort>();
		seqs = new LinkedList<SMTFunction>();
		model = new Model();
		objFunctions = new HashMap<String,SMTSort>();
		
	}
	
	public List<String> getAllIDs(int size){
		
		List<String> result = new LinkedList<String>();
		
		for(int i = 0 ; i < Math.pow(2, size); ++i){
			String val = Integer.toBinaryString(i);
			while(val.length() < size){
				val = "0"+val;
			}
			val = "#b"+val;
			
			result.add(val);
			
			
		}
		
		return result;
		
		
		
		
		
		
	}

	public ProblemTypeInformation getTypes() {
		return types;
	}



	public void setTypes(ProblemTypeInformation types) {
		this.types = types;
	}



	/**
	 * @return the state
	 */
	public int getState() {
		return state;
	}

	private void finishBasicQueries(Pipe<SolverCommunication> pipe){

		processBasicQueries();
		generateArrayQueries();
		state = ARRAYFIELDS;
		
		
		
		if(queries.size() > 0){
			Query q = queries.get(currentQuery);		
			pipe.sendMessage(q.getQuery());
			
		}
		else{
			
			state = SEQ;
			generateSeqQueries();
			
			if(queries.size() > 0){
				Query q = queries.get(currentQuery);		
				pipe.sendMessage(q.getQuery());
			}
			else{
				model.processSequenceNames();
				model.processObjectNames();
				state = FINISHED;
				pipe.sendMessage("(exit)\n");
			}
			
			
			
		}	
		
	}
	


	private void processBasicQueries() {
		model.setTypes(types);


		for(Query q : queries){

			if(q instanceof ConstantQuery){
				ConstantQuery cq = (ConstantQuery) q;
				model.addConstant(cq.getConstantID(), cq.getResult());				
			}
			else if(q instanceof FieldQuery){
				FieldQuery fq = (FieldQuery) q;

				String heapID = fq.getHeapID();
				String objectID = fq.getObjectID();
				
				
				String fieldID = fq.getFieldID();
				String value = fq.getResult();

				List<Heap> heaps = model.getHeaps();

				Heap heap = new Heap(heapID);

				if(heaps.contains(heap)){
					heap = heaps.get(heaps.indexOf(heap));
				}
				else{
					model.addHeap(heap);
				}			

				List<ObjectVal> objects = heap.getObjects();
				ObjectVal ov = new ObjectVal(objectID);
		
				if(objects.contains(ov)){
					ov = objects.get(objects.indexOf(ov));
				}
				else{
					heap.add(ov);
					ov.setSort(objectSorts.get(objectID));
				}

				ov.put(fieldID, value);				
			}
			else if(q instanceof LocSetQuery){
				LocSetQuery lq = (LocSetQuery) q;

				String locsetID = lq.getLocSetID();				
				
				String objectID = lq.getObjectID();
				
				String fieldID = lq.getFieldID();
				String value = lq.getResult();

				LocationSet ls = new LocationSet(locsetID);
				List<LocationSet> locsets = model.getLocsets();

				if(locsets.contains(ls)){
					ls = locsets.get(locsets.indexOf(ls));
				}
				else{
					model.addLocationSet(ls);
				}
				if(value.equals("true")){
					ls.add(new Location(objectID, fieldID));	
				}

			}
			else if(q instanceof ObjectLengthQuery){
				ObjectLengthQuery oq = (ObjectLengthQuery) q;
				String objectID = oq.getObjectID();
				
				int result = Integer.parseInt(oq.getResult());
				
				long intBound = (long) Math.pow(2,types.getSettings().getIntBound());
				
				if(result >= intBound/2){
					result -= intBound;
				}


				for(Heap h : model.getHeaps()){

					for(ObjectVal ov : h.getObjects()){

						if(ov.getName().equals(objectID)){

							ov.setLength(result);
						}
					}
				}
			}
			else if(q instanceof SeqLengthQuery){
				SeqLengthQuery sq = (SeqLengthQuery) q;
				
				String seqId = sq.getSeqID();
				
				
				
				int result = Integer.parseInt(sq.getResult());

				long intBound = (long) Math.pow(2,types.getSettings().getIntBound());
				
				if(result >= intBound/2){
					result -= intBound;
				}
				
				
				
				Sequence s = new Sequence(result, seqId);
				model.addSequence(s);			
				
			}
			else if(q instanceof FunValueQuery){
				FunValueQuery iq = (FunValueQuery) q;
				
				
				String heapID = iq.getHeapID();
				String objectID = iq.getObjectID();
				String fun = iq.getFunctionID();
				String result = iq.getResult();
				
				List<Heap> heaps = model.getHeaps();

				Heap heap = new Heap(heapID);

				if(heaps.contains(heap)){
					heap = heaps.get(heaps.indexOf(heap));
				}
				else{
					model.addHeap(heap);
				}			

				List<ObjectVal> objects = heap.getObjects();
				ObjectVal ov = new ObjectVal(objectID);
		
				if(objects.contains(ov)){
					ov = objects.get(objects.indexOf(ov));
				}
				else{
					heap.add(ov);
					ov.setSort(objectSorts.get(objectID));
				}
				
				SMTSort sort = objFunctions.get(fun);
				if(sort.getId().equals(SMTObjTranslator.ANY_SORT)){
					result = model.processAnyValue(result);
				}
				else{
					result = model.processConstantValue(result, sort);
				}
				
				ov.putFunValue(fun, result);
				
				
				
			}
			else if(q instanceof ExactInstanceQuery){
				ExactInstanceQuery eq = (ExactInstanceQuery) q;
				
				String objectID = eq.getObjectId();
				
				
				
				boolean result = eq.getResult().equals("true");
				
				for(Heap h : model.getHeaps()){
					
					
					for(ObjectVal ov : h.getObjects()){
						
						if(ov.getName().equals(objectID)){
							
							ov.setExactInstance(result);
							
						}
						
					}				
					
				}
				
				
				
			}
			
			


		}


		
		model.processConstantsAndFieldValues();

	}

	@Override
	public void messageIncoming(Pipe<SolverCommunication> pipe, String message,
			int type) {	

		//System.out.println("MQ: " + message);

		if(state == WORKING){


			if(currentQuery >= 0 && currentQuery < queries.size()){

				Query q = queries.get(currentQuery);
				q.setResult(message);

				++currentQuery;
				if(currentQuery >= queries.size()){
					finishBasicQueries(pipe);
					return;
				}
				q = queries.get(currentQuery); 
				pipe.sendMessage(q.getQuery());			
			}
			else{
				finishBasicQueries(pipe);
			}
		}
		else if(state == ARRAYFIELDS){
			if(currentQuery >= 0 && currentQuery < queries.size()){

				Query q = queries.get(currentQuery);
				q.setResult(message);

				++currentQuery;
				if(currentQuery >= queries.size()){
					finishArrayQueries(pipe);
					return;
				}
				q = queries.get(currentQuery); 
				pipe.sendMessage(q.getQuery());			
			}
			else{
				finishArrayQueries(pipe);
			}
		}
		else if(state == TYPES){
			if(currentQuery >= 0 && currentQuery < queries.size()){

				Query q = queries.get(currentQuery);
				q.setResult(message);

				++currentQuery;
				if(currentQuery >= queries.size()){
					finishTypesQueries(pipe);
					return;
				}
				q = queries.get(currentQuery); 
				pipe.sendMessage(q.getQuery());			
			}
			else{
				finishTypesQueries(pipe);
			}
		}
		else if(state == SEQ){
			if(currentQuery >= 0 && currentQuery < queries.size()){

				Query q = queries.get(currentQuery);
				q.setResult(message);

				++currentQuery;
				if(currentQuery >= queries.size()){
					finishSeqQueries(pipe);
					return;
				}
				q = queries.get(currentQuery); 
				pipe.sendMessage(q.getQuery());			
			}
			else{
				finishSeqQueries(pipe);
			}
		}
		



	}

	private void finishTypesQueries(Pipe<SolverCommunication> pipe) {
		processTypesQueries();
		startBasicQueries(pipe);
		
	}
	
	private void finishSeqQueries(Pipe<SolverCommunication> pipe){
		processSeqQueries();
		model.processSeqValues();
		model.processSequenceNames();
		model.processObjectNames();
		state = FINISHED;
		pipe.sendMessage("(exit)\n");
		
	}



	private void startBasicQueries(Pipe<SolverCommunication> pipe) {
		generateBasicQueries();
		Query q = queries.get(currentQuery);
		state = WORKING;
		pipe.sendMessage(q.getQuery());
	}



	private void processTypesQueries() {
		for(Query q : queries){
			
			if(q instanceof ObjectTypeQuery){
				ObjectTypeQuery oq = (ObjectTypeQuery) q;
				String objectID = oq.getObjectId();
				Sort s = oq.getSort();
				String result = oq.getResult();
				
				if(result.equals("true")){
					Sort t = objectSorts.get(objectID);
					
					if(t == null || s.extendsTrans(t)){
						objectSorts.put(objectID, s);
					}
					else if(t.isAbstract() && !s.isAbstract()){
						objectSorts.put(objectID, s);
					}
					
					
				}
				
			}
			
			
		}
		
	}



	private void finishArrayQueries(Pipe<SolverCommunication> pipe) {
		
		processArrayQueries();
		state = SEQ;
		generateSeqQueries();
		if(queries.size()>0){
			pipe.sendMessage(queries.get(currentQuery).getQuery());
		}
		else{
			model.processSequenceNames();
			model.processObjectNames();
			state = FINISHED;
			pipe.sendMessage("(exit)\n");
		}
		
		
	}



	private void processArrayQueries() {
		for(Query q : queries){
			
			if(q instanceof ArrayFieldQuery){
				
				ArrayFieldQuery aq = (ArrayFieldQuery) q;
				
				String heapID = aq.getHeapID();
				String objectID = aq.getObjectID();
				String result = aq.getResult();
				Heap heap = new Heap(heapID);
				Heap h = model.getHeaps().get(model.getHeaps().indexOf(heap));
				
				ObjectVal ov = new ObjectVal(objectID);
				
				ObjectVal o = h.getObjects().get(h.getObjects().indexOf(ov));
				
				//System.out.println("Set value for: "+objectID+" field "+aq.getIndex());
				
				
				
				o.setArrayValue(aq.getIndex(), result);
				
				
				
				
				
			}
			
			
		}
		
		model.processArrayValues();
		
		
	}
	
	private void processSeqQueries(){
		for(Query q : queries){
			if(q instanceof SeqFieldQuery){
				SeqFieldQuery sq = (SeqFieldQuery) q;
				
				
				Sequence s = sq.getSeq();
				int i = sq.getIndex();
				String result = sq.getResult();
				
				s.set(i, result);
				
				
				
				
			}
		}
	}



	public void start(Pipe<SolverCommunication> pipe){
		//pipe.addListener(this);
		generateTypeQueries();
		currentQuery = 0;
		Query q = queries.get(currentQuery);
		state = TYPES;
		pipe.sendMessage(q.getQuery());		

	}

	public boolean isWorking(){
		return state == WORKING || state == ARRAYFIELDS;
	}


	@Override
	public void exceptionOccurred(Pipe<SolverCommunication> pipe,
			Throwable exception) {


	}

}
