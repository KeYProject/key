/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.util.*;

import de.uka.ilkd.key.smt.communication.Pipe;
import de.uka.ilkd.key.smt.lang.SMTFunction;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.lang.Util;
import de.uka.ilkd.key.smt.model.*;

import org.key_project.logic.sort.Sort;

/**
 * Represents a query directed to towards the z3 solver.
 *
 * @author mihai
 */
interface Query {
    String SELECT_ID = "select_";

    /**
     * Stores the result from the z3 solver.
     */
    void setResult(String s);

    /**
     * Returns the command that is to be handed over to the z3 solver.
     */
    String getQuery();

    /**
     * Returns the stored result.
     */
    String getResult();
}


abstract class AbstractQuery implements Query {
    protected String result;

    protected AbstractQuery() {
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
 *
 * @author mihai
 */
class ConstantQuery extends AbstractQuery {
    public ConstantQuery(String constantID) {
        super();
        this.constantID = constantID;
    }

    private final String constantID;

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

    @Override
    public void setResult(String s) {
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
 *
 * @author mihai
 */
class SeqFieldQuery extends AbstractQuery {
    private final Sequence seqID;

    private final int index;
    private final int intBound;

    public SeqFieldQuery(Sequence seq, int index, int bound) {
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
        String val = "(_ bv" + index + " " + intBound + ")";
        String q = enclose(SMTObjTranslator.SEQ_GET + " " + seqID.getName() + " " + val);
        q = enclose(q);
        return getVal(q);
    }

    @Override
    public void setResult(String s) {
        String[] parts = split(s);
        result = parts[5];
    }

    static String[] split(String s) {
        s = s.replace("(", "");
        s = s.replace(")", "");
        s = s.replace("  ", " ");
        s = s.replace("  ", " ");
        s = s.replace("|", "");
        s = s.trim();
        return s.split(" ");
    }
}


/**
 * Query for the value of an array field of an object in a heap.
 *
 * @author mihai
 */
class ArrayFieldQuery extends AbstractQuery {
    private final String heapID;
    private final String objectID;
    private final int index;
    private final int intBound;


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
        String val = "(_ bv" + index + " " + intBound + ")";
        String arr = enclose("arr " + val);
        String q = enclose(SELECT_ID + " " + heapID + " " + objectID + " " + arr);
        q = enclose(q);
        return getVal(q);
    }

    @Override
    public void setResult(String s) {
        var parts = SeqFieldQuery.split(s);
        result = parts[7];
    }
}


/**
 * Query for the value of a named field of an object in a heap.
 *
 * @author mihai
 */
class FieldQuery extends AbstractQuery {

    private final String heapID;
    private final String objectID;
    private final String fieldID;


    public FieldQuery(String heapID, String objectID, String fieldID) {
        super();
        this.heapID = heapID;
        this.objectID = objectID;
        this.fieldID = fieldID;
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

        String q = enclose(SELECT_ID + " " + heapID + " " + objectID + " " + fieldID);

        q = enclose(q);

        return getVal(q);
    }

    @Override
    public void setResult(String s) {
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
 *
 * @author mihai
 */
class LocSetQuery extends AbstractQuery {


    private final String locSetID;
    private final String objectID;
    private final String fieldID;


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
        String q =
            enclose(SMTObjTranslator.ELEMENTOF + " " + objectID + " " + fieldID + " " + locSetID);
        q = enclose(q);
        return getVal(q);
    }

    @Override
    public void setResult(String s) {
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
 *
 * @author mihai
 */
class SeqLengthQuery extends AbstractQuery {

    private final String seqID;

    public String getSeqID() {
        return seqID;
    }


    public SeqLengthQuery(String objectID) {
        super();
        this.seqID = objectID;
    }

    @Override
    public String getQuery() {

        String q = enclose(SMTObjTranslator.SEQ_LEN + " " + seqID);
        q = enclose(q);
        return getVal(q);


    }

    @Override
    public void setResult(String s) {
        s = s.replace("(", "");
        s = s.replace(")", "");
        s = s.replace(SMTObjTranslator.SEQ_LEN, "");
        s = s.replace("|", "");
        s = s.replace("  ", " ");
        s = s.trim();
        String[] parts = s.split(" ");
        String value = parts[1];
        int x;
        if (value.startsWith("#x")) {
            value = value.replace("#x", "");
            x = Integer.parseInt(value, 16);
        } else {
            value = value.replace("#b", "");
            x = Integer.parseInt(value, 2);
        }

        value = Integer.toString(x);

        result = value;


    }

}


/**
 * Query for finding out the length of an object.
 *
 * @author mihai
 */
class ObjectLengthQuery extends AbstractQuery {

    private final String objectID;


    public String getObjectID() {
        return objectID;
    }


    public ObjectLengthQuery(String objectID) {
        super();
        this.objectID = objectID;
    }

    @Override
    public String getQuery() {

        String q = enclose(SMTObjTranslator.LENGTH + " " + objectID);
        q = enclose(q);
        return getVal(q);


    }

    @Override
    public void setResult(String s) {
        s = s.replace("(", "");
        s = s.replace(")", "");
        s = s.replace(SMTObjTranslator.LENGTH, "");
        s = s.replace("|", "");
        s = s.replace("  ", " ");
        s = s.trim();
        String[] parts = s.split(" ");
        String value = parts[1];
        int x;
        if (value.startsWith("#x")) {
            value = value.replace("#x", "");
            x = Integer.parseInt(value, 16);
        } else {
            value = value.replace("#b", "");
            x = Integer.parseInt(value, 2);
        }

        value = Integer.toString(x);

        result = value;


    }

}


/**
 * Query for finding out the value of a function(classinvariant or model field) for an object in a
 * heap.
 *
 * @author mihai
 */
class FunValueQuery extends AbstractQuery {

    private final String objectId;

    private final String heapID;

    private final String functionID;


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

    @Override
    public void setResult(String s) {
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
 *
 * @author mihai
 */
class ExactInstanceQuery extends AbstractQuery {
    private final String objectId;
    private final Sort sort;


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


        String typeof =
            Util.processName(SMTObjTranslator.getExactInstanceName(sort.name().toString()));

        String q = enclose(typeof + " " + objectId);
        q = enclose(q);
        q = getVal(q);


        return q;


    }

    @Override
    public void setResult(String s) {
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
 *
 * @author mihai
 */
class ObjectTypeQuery extends AbstractQuery {

    private final String objectId;
    private final Sort sort;


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

        String typeof =
            Util.processName(SMTObjTranslator.getTypePredicateName(sort.name().toString()));

        String q = enclose(typeof + " " + objectId);
        q = enclose(q);
        return getVal(q);
    }

    @Override
    public void setResult(String s) {
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
 * Class for sending queries to the solver and extracting the relevant information regarding the
 * model.
 *
 * @author mihai
 */
public class ModelExtractor {

    public static final int DEFAULT = 0;
    public static final int TYPES = 4;
    public static final int WORKING = 1;
    public static final int ARRAYFIELDS = 2;
    public static final int FINISHED = 3;
    public static final int SEQ = 5;

    private final Model model;


    private int state;


    private final List<SMTFunction> heaps;
    private final List<SMTFunction> objects;
    private final List<SMTFunction> fields;
    private final List<SMTFunction> locsets;
    private final List<SMTFunction> ints;
    private final List<SMTFunction> bools;
    private final List<SMTFunction> seqs;
    private final Map<String, SMTSort> objFunctions;

    private ProblemTypeInformation types;
    private final Map<String, Sort> objectSorts;

    private List<Query> queries;
    private int currentQuery;
    private int intBound;


    public void addFunction(SMTFunction f) {
        if (f.getDomainSorts().isEmpty()) {
            switch (f.getImageSort().getId()) {
                case SMTObjTranslator.HEAP_SORT -> heaps.add(f);
                case SMTObjTranslator.FIELD_SORT -> fields.add(f);
                case SMTObjTranslator.LOCSET_SORT -> locsets.add(f);
                case SMTObjTranslator.OBJECT_SORT -> objects.add(f);
                case SMTObjTranslator.BINT_SORT -> ints.add(f);
                case SMTObjTranslator.SEQ_SORT -> seqs.add(f);
                default -> bools.add(f);
            }
        } else if (f.getDomainSorts().size() == 2) {

            SMTSort s1 = f.getDomainSorts().get(0);
            SMTSort s2 = f.getDomainSorts().get(1);

            if (s1.getId().equals(SMTObjTranslator.HEAP_SORT)
                    && s2.getId().equals(SMTObjTranslator.OBJECT_SORT)) {

                objFunctions.put(f.getId(), f.getImageSort());


            }


        }
    }


    public Model getModel() {
        return model;
    }

    private void generateTypeQueries() {
        queries = new LinkedList<>();
        currentQuery = 0;

        for (String objectID : getAllIDs((int) types.getSettings().getObjectBound())) {
            for (Sort s : types.getJavaSorts()) {
                Query q = new ObjectTypeQuery(objectID, s);
                queries.add(q);
            }
        }
    }


    private void generateBasicQueries() {
        queries = new LinkedList<>();
        currentQuery = 0;
        // generate constant queries

        List<SMTFunction> constants = new LinkedList<>();
        constants.addAll(objects);
        constants.addAll(locsets);
        constants.addAll(bools);
        constants.addAll(fields);
        constants.addAll(ints);
        constants.addAll(heaps);
        constants.addAll(seqs);

        for (SMTFunction f : constants) {
            String constantID = f.getId();
            ConstantQuery q = new ConstantQuery(constantID);
            queries.add(q);
        }

        // generate heap queries

        for (SMTFunction h : heaps) {
            String heapID = h.getId();


            for (String objectID : getAllIDs((int) types.getSettings().getObjectBound())) {

                // generate the obj inv query
                for (String fun : objFunctions.keySet()) {
                    FunValueQuery iq = new FunValueQuery(objectID, heapID, fun);
                    queries.add(iq);
                }


                // generate the named fields queries
                for (SMTFunction f : fields) {
                    String fieldID = f.getId();

                    Sort s = objectSorts.get(objectID);
                    Set<String> fields;
                    if (s == null) {
                        fields = types.getFieldsForSort("java.lang.Object");
                    } else {
                        fields = types.getFieldsForSort(s);
                    }

                    if (fields.contains(fieldID)) {
                        Query q = new FieldQuery(heapID, objectID, fieldID);
                        queries.add(q);
                    }
                }
            }
        }

        // generate exactInstance queries

        for (String objectID : getAllIDs((int) types.getSettings().getObjectBound())) {

            if (objectID.equals("#o0")) {
                continue;
            }


            Sort s = objectSorts.get(objectID);
            if (s != null) {
                ExactInstanceQuery eq = new ExactInstanceQuery(objectID, s);
                queries.add(eq);
            }


        }


        // generate locset Queries
        int locsetSize = (int) types.getSettings().getLocSetBound();
        for (String locSetID : getAllIDs(locsetSize)) {

            for (String objectID : getAllIDs((int) types.getSettings().getObjectBound())) {

                int fieldSize = (int) types.getSort(SMTObjTranslator.FIELD_SORT).getBitSize();
                int intBound = (int) types.getSort(SMTObjTranslator.BINT_SORT).getBound();


                int i = 0;
                for (String fieldID : getAllIDs(fieldSize)) {

                    if (i++ >= intBound / 2) {
                        break;
                    }

                    Query q = new LocSetQuery(locSetID, objectID, fieldID);
                    queries.add(q);
                }

                for (SMTFunction f : fields) {
                    String fieldID = f.getId();
                    Query q = new LocSetQuery(locSetID, objectID, fieldID);
                    queries.add(q);
                }

            }

        }

        // generate Object length queries

        for (String objectID : getAllIDs((int) types.getSettings().getObjectBound())) {


            Query q = new ObjectLengthQuery(objectID);
            queries.add(q);


        }

        // generate Seq len query

        for (String seqID : getAllIDs((int) types.getSettings().getSeqBound())) {

            Query q = new SeqLengthQuery(seqID);
            queries.add(q);
        }

    }

    private void generateArrayQueries() {
        queries = new LinkedList<>();
        currentQuery = 0;

        for (Heap h : model.getHeaps()) {
            for (ObjectVal ov : h.getObjects()) {
                if (ov.getSort() == null) {
                    continue;
                }

                String sortName = ov.getSort().name().toString();
                if (!sortName.endsWith("[]")) {
                    continue;
                }

                for (int i = 0; i < ov.getLength(); ++i) {
                    Query q = new ArrayFieldQuery(h.getName(), ov.getName(), i, intBound);
                    queries.add(q);
                }
            }
        }
    }

    private void generateSeqQueries() {
        queries = new LinkedList<>();
        currentQuery = 0;

        for (Sequence s : model.getSequences()) {

            for (int i = 0; i < s.getLength(); ++i) {

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
        heaps = new LinkedList<>();
        objects = new LinkedList<>();
        fields = new LinkedList<>();
        ints = new LinkedList<>();
        locsets = new LinkedList<>();
        bools = new LinkedList<>();
        objectSorts = new HashMap<>();
        seqs = new LinkedList<>();
        model = new Model();
        objFunctions = new HashMap<>();

    }

    public List<String> getAllIDs(int size) {

        List<String> result = new LinkedList<>();

        for (int i = 0; i < Math.pow(2, size); ++i) {
            StringBuilder val = new StringBuilder(Integer.toBinaryString(i));
            while (val.length() < size) {
                val.insert(0, "0");
            }
            val.insert(0, "#b");
            result.add(val.toString());
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

    private void finishBasicQueries(Pipe pipe) throws IOException {
        processBasicQueries();
        generateArrayQueries();
        state = ARRAYFIELDS;

        if (!queries.isEmpty()) {
            Query q = queries.get(currentQuery);
            pipe.sendMessage(q.getQuery());

        } else {

            state = SEQ;
            generateSeqQueries();

            if (!queries.isEmpty()) {
                Query q = queries.get(currentQuery);
                pipe.sendMessage(q.getQuery());
            } else {
                model.processSequenceNames();
                model.processObjectNames();
                state = FINISHED;
                pipe.sendMessage("(exit)\n");
            }
        }
    }


    private void processBasicQueries() {
        model.setTypes(types);


        for (Query q : queries) {

            if (q instanceof ConstantQuery cq) {
                model.addConstant(cq.getConstantID(), cq.getResult());
            } else if (q instanceof FieldQuery fq) {

                String heapID = fq.getHeapID();
                String objectID = fq.getObjectID();


                String fieldID = fq.getFieldID();
                String value = fq.getResult();

                List<Heap> heaps = model.getHeaps();

                Heap heap = new Heap(heapID);

                if (heaps.contains(heap)) {
                    heap = heaps.get(heaps.indexOf(heap));
                } else {
                    model.addHeap(heap);
                }

                List<ObjectVal> objects = heap.getObjects();
                ObjectVal ov = new ObjectVal(objectID);

                if (objects.contains(ov)) {
                    ov = objects.get(objects.indexOf(ov));
                } else {
                    heap.add(ov);
                    ov.setSort(objectSorts.get(objectID));
                }

                ov.put(fieldID, value);
            } else if (q instanceof LocSetQuery lq) {

                String locsetID = lq.getLocSetID();

                String objectID = lq.getObjectID();

                String fieldID = lq.getFieldID();
                String value = lq.getResult();

                LocationSet ls = new LocationSet(locsetID);
                List<LocationSet> locsets = model.getLocsets();

                if (locsets.contains(ls)) {
                    ls = locsets.get(locsets.indexOf(ls));
                } else {
                    model.addLocationSet(ls);
                }
                if (value.equals("true")) {
                    ls.add(new Location(objectID, fieldID));
                }

            } else if (q instanceof ObjectLengthQuery oq) {
                String objectID = oq.getObjectID();

                int result = Integer.parseInt(oq.getResult());

                long intBound = (long) Math.pow(2, types.getSettings().getIntBound());

                if (result >= intBound / 2) {
                    result -= intBound;
                }


                for (Heap h : model.getHeaps()) {

                    for (ObjectVal ov : h.getObjects()) {

                        if (ov.getName().equals(objectID)) {

                            ov.setLength(result);
                        }
                    }
                }
            } else if (q instanceof SeqLengthQuery sq) {

                String seqId = sq.getSeqID();


                int result = Integer.parseInt(sq.getResult());

                long intBound = (long) Math.pow(2, types.getSettings().getIntBound());

                if (result >= intBound / 2) {
                    result -= intBound;
                }


                Sequence s = new Sequence(result, seqId);
                model.addSequence(s);

            } else if (q instanceof FunValueQuery iq) {


                String heapID = iq.getHeapID();
                String objectID = iq.getObjectID();
                String fun = iq.getFunctionID();
                String result = iq.getResult();

                List<Heap> heaps = model.getHeaps();

                Heap heap = new Heap(heapID);

                if (heaps.contains(heap)) {
                    heap = heaps.get(heaps.indexOf(heap));
                } else {
                    model.addHeap(heap);
                }

                List<ObjectVal> objects = heap.getObjects();
                ObjectVal ov = new ObjectVal(objectID);

                if (objects.contains(ov)) {
                    ov = objects.get(objects.indexOf(ov));
                } else {
                    heap.add(ov);
                    ov.setSort(objectSorts.get(objectID));
                }

                SMTSort sort = objFunctions.get(fun);
                if (sort.getId().equals(SMTObjTranslator.ANY_SORT)) {
                    result = model.processAnyValue(result);
                } else {
                    result = model.processConstantValue(result, sort);
                }

                ov.putFunValue(fun, result);


            } else if (q instanceof ExactInstanceQuery eq) {

                String objectID = eq.getObjectId();


                boolean result = eq.getResult().equals("true");

                for (Heap h : model.getHeaps()) {


                    for (ObjectVal ov : h.getObjects()) {

                        if (ov.getName().equals(objectID)) {

                            ov.setExactInstance(result);

                        }

                    }

                }


            }


        }


        model.processConstantsAndFieldValues();

    }

    public void messageIncoming(Pipe pipe, String message) throws IOException {
        if (state == WORKING) {
            if (currentQuery >= 0 && currentQuery < queries.size()) {
                Query q = queries.get(currentQuery);
                q.setResult(message);

                ++currentQuery;
                if (currentQuery >= queries.size()) {
                    finishBasicQueries(pipe);
                    return;
                }
                q = queries.get(currentQuery);
                pipe.sendMessage(q.getQuery());
            } else {
                finishBasicQueries(pipe);
            }
        } else if (state == ARRAYFIELDS) {
            if (currentQuery >= 0 && currentQuery < queries.size()) {

                Query q = queries.get(currentQuery);
                q.setResult(message);

                ++currentQuery;
                if (currentQuery >= queries.size()) {
                    finishArrayQueries(pipe);
                    return;
                }
                q = queries.get(currentQuery);
                pipe.sendMessage(q.getQuery());
            } else {
                finishArrayQueries(pipe);
            }
        } else if (state == TYPES) {
            if (currentQuery >= 0 && currentQuery < queries.size()) {

                Query q = queries.get(currentQuery);
                q.setResult(message);

                ++currentQuery;
                if (currentQuery >= queries.size()) {
                    finishTypesQueries(pipe);
                    return;
                }
                q = queries.get(currentQuery);
                pipe.sendMessage(q.getQuery());
            } else {
                finishTypesQueries(pipe);
            }
        } else if (state == SEQ) {
            if (currentQuery >= 0 && currentQuery < queries.size()) {

                Query q = queries.get(currentQuery);
                q.setResult(message);

                ++currentQuery;
                if (currentQuery >= queries.size()) {
                    finishSeqQueries(pipe);
                    return;
                }
                q = queries.get(currentQuery);
                pipe.sendMessage(q.getQuery());
            } else {
                finishSeqQueries(pipe);
            }
        }
    }

    private void finishTypesQueries(Pipe pipe) throws IOException {
        processTypesQueries();
        startBasicQueries(pipe);

    }

    private void finishSeqQueries(Pipe pipe) throws IOException {
        processSeqQueries();
        model.processSeqValues();
        model.processSequenceNames();
        model.processObjectNames();
        state = FINISHED;
        pipe.sendMessage("(exit)\n");

    }


    private void startBasicQueries(Pipe pipe) throws IOException {
        generateBasicQueries();
        Query q = queries.get(currentQuery);
        state = WORKING;
        pipe.sendMessage(q.getQuery());
    }


    private void processTypesQueries() {
        for (Query q : queries) {
            if (q instanceof ObjectTypeQuery oq) {
                String objectID = oq.getObjectId();
                Sort s = oq.getSort();
                String result = oq.getResult();

                if (result.equals("true")) {
                    Sort t = objectSorts.get(objectID);
                    if (t == null || s.extendsTrans(t) || (t.isAbstract() && !s.isAbstract())) {
                        objectSorts.put(objectID, s);
                    }
                }
            }
        }
    }


    private void finishArrayQueries(Pipe pipe) throws IOException {

        processArrayQueries();
        state = SEQ;
        generateSeqQueries();
        if (!queries.isEmpty()) {
            pipe.sendMessage(queries.get(currentQuery).getQuery());
        } else {
            model.processSequenceNames();
            model.processObjectNames();
            state = FINISHED;
            pipe.sendMessage("(exit)\n");
        }


    }


    private void processArrayQueries() {
        for (Query q : queries) {
            if (q instanceof ArrayFieldQuery aq) {

                String heapID = aq.getHeapID();
                String objectID = aq.getObjectID();
                String result = aq.getResult();
                Heap heap = new Heap(heapID);
                Heap h = model.getHeaps().get(model.getHeaps().indexOf(heap));

                ObjectVal ov = new ObjectVal(objectID);
                ObjectVal o = h.getObjects().get(h.getObjects().indexOf(ov));
                o.setArrayValue(aq.getIndex(), result);
            }
        }
        model.processArrayValues();
    }

    private void processSeqQueries() {
        for (Query q : queries) {
            if (q instanceof SeqFieldQuery sq) {


                Sequence s = sq.getSeq();
                int i = sq.getIndex();
                String result = sq.getResult();

                s.set(i, result);


            }
        }
    }

    public void start(Pipe pipe) throws IOException {
        generateTypeQueries();
        if (!queries.isEmpty()) {
            currentQuery = 0;
            Query q = queries.get(currentQuery);
            state = TYPES;
            pipe.sendMessage(q.getQuery());
        } else {
            finishTypesQueries(pipe);
        }


    }

    public boolean isWorking() {
        return state == WORKING || state == ARRAYFIELDS;
    }

}
