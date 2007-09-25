package de.uka.ilkd.key.rule;

import java.io.*;
import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.visitor.ProgramSVCollector;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.EnvInput;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYFileForTests;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.KeYResourceManager;


/**
Automated use to prove sets of taclets

To actually use all this on a set of taclets you have to do the
following:  Put the taclets you are interested in into a
``.key'' file, e.g.\ called ``rules.key''. You start the generation of
the Maude input in this case by running ``bin/runJava
de.uka.ilkd.key.rule.CheckPrgTransfSoundness rules.key input.maude''
where the result gets put into the file ``input.maude''. Then you start
Maude with the output written directly to a file, say ``result.txt'' by
running your version of maude, in linux e.g.\ with ``maude-linux >
result.txt''. Then you load the modified Maude Java Semantics which you
can get from my homepage ``i12www.ira.uka.de/~rsasse'' with ``load
java-es-m-modified.maude'' and will get some warnings printed on the
monitor which you can safely ignore. When those are complete you load
the input by typing ``load input.maude'' and then wait for around a
minute to be on the safe side, or take a look at whether the processor
is working, if not it is probably done. Then end Maude by typing ``q''.

*/

public class CheckPrgTransfSoundness {


    private static final JavaProfile JAVA_PROFILE = new JavaProfile();
    
    // These two counters are basically used to give every case of every
    // taclet a unique identification by the combination of the two
    // integers.
    private static int caseCounter = 0;
    private static int tacletCounter = 0;

    // This variable contains the then-current taclet at all points in
    // the code when such a taclet exists.
    private static Taclet currentTaclet = null;

    // This variable contains the list of new variables, when
    // applicable, depending on each taclet.
    private static ListOfNewVarcond newvars = null;

    // This is a Map from SchemaVariables to Restrictions.
    private static Map svToRestriction = new HashMap();

    // Constant representing the case with no restriction.
    private static Restriction RESTRICTNONE = new RestrictionNone();

    // Three strings which are later on put into the Maude
    // configuration.
    private static String findString;
    private static String replaceWithString;
    private static String addNewString;

    // These strings are here to distinguish the cases for each
    // SchemaVariable, they are necessary to create the fitting string
    // for the Maude configuration generation.
    private static final String ATTRIBVAL =
        new String("Attribute, value.");
    private static final String ATTRIBINT =
        new String("Attribute, integer.");
    private static final String ATTRIBBOOL =
        new String("Attribute, boolean.");
    private static final String LOCALVARVAL =
        new String("Local Variable, value.");
    private static final String LOCALVARINT =
        new String("Local Variable, integer.");
    private static final String LOCALVARBOOL =
        new String("Local Variable, boolean.");
    private static final String LOCALVARATT =
        new String("Local Variable, object with attribute.");
    private static final String ATTOBJWOTHISVAL =
        new String("Attribute of the current object without this, value.");
    private static final String ATTOBJWOTHISINT =
        new String("Attribute of the current object without this, integer.");
    private static final String ATTOBJWOTHISBOOL =
        new String("Attribute of the current object without this, boolean.");
    private static final String ATTOBJWOTHISATT =
        new String("Attribute of the current object without this, "
                   +"object with attribute.");
    private static final String ATTOBJWITHTHISVAL =
        new String("Attribute of the current object with this, value.");
    private static final String ATTOBJWITHTHISINT =
        new String("Attribute of the current object with this, integer.");
    private static final String ATTOBJWITHTHISBOOL =
        new String("Attribute of the current object with this, boolean.");
    private static final String ATTOBJWITHTHISATT =
        new String("Attribute of the current object with this, "
                   +"object with attribute.");
    private static final String STATATTTYPEREFVAL =
        new String("Static attribute with a type reference first, value.");
    private static final String STATATTTYPEREFINT =
        new String("Static attribute with a type reference first, integer.");
    private static final String STATATTTYPEREFBOOL =
        new String("Static attribute with a type reference first, boolean.");
    private static final String STATATTTYPEREFATT =
        new String("Static attribute with a type reference first, "
                   +"object with attribute.");
    private static final String STATATTOBJREFVAL =
        new String("Static attribute with a program variable, "
                   +"in this case an object reference, first. Value.");
    private static final String STATATTOBJREFINT =
        new String("Static attribute with a program variable, "
                   +"in this case an object reference, first. Integer.");
    private static final String STATATTOBJREFBOOL =
        new String("Static attribute with a program variable, "
                   +"in this case an object reference, first. Boolean.");
    private static final String STATATTOBJREFATT =
        new String("Static attribute with a program variable, "
                   +"in this case an object reference, first. "
                   +"Object with attribute.");
    private static final String LITERALINT =
        new String("Generic integer literal.");
    private static final String LITERALVALUE =
        new String("Generic value literal.");
    private static final String LITERALBOOL =
        new String("Generic boolean literal.");

    private static final String EXPRESSIONVAL =
        new String("Expression with VALUE return");
    private static final String EXPRESSIONINT =
        new String("Expression with INTEGER return");
    private static final String EXPRESSIONBOOL =
        new String("Expression with BOOLEAN return");
    private static final String EXPRESSIONATT =
        new String("Expression with an object with attribute return");

    private static String[] ruleFiles = new String[]{"../proof/rules/ruleSetsDeclarations.key", "../proof/rules/javaRules.key"};

    // Used to write the strings out into a file.
    private static FileWriter fW;

    private CheckPrgTransfSoundness(){}

    // This method parses the file which includes all taclets. It
    // creates a "SetOfTaclet" set which includes the taclets.
    public static SetOfTaclet parseTaclets() {

        Set checkTacsName = new HashSet();

        try {
            BufferedReader r = new BufferedReader
                (new FileReader
                 (KeYResourceManager.getManager().getResourceFile
                  (CheckPrgTransfSoundness.class,
                   "../proof/rules/checkTacletsWithMaudeList.txt").getFile()));
            for (String jl = r.readLine();(jl != null); jl = r.readLine()) {
                if ((jl.length() == 0) || (jl.charAt(0) == '#')) {
                    continue;
                }
                // add the "jl" string to the set of names of
                // the taclets which are to be checked
                checkTacsName.add(jl);
            }
        }
        // catch all exceptions
        catch(Exception e) {
            System.err.println("Exception occurred while parsing "
                               +"../system/resources/de/uka/ilkd/key/proof/rules/checkTacletsWithMaudeList.txt"
                               +"\n");
            e.printStackTrace();
            System.exit(-1);
            return null;
        }

        SetOfTaclet rules = SetAsListOfTaclet.EMPTY_SET;
        File allTacletsFile = null;
        try {
            allTacletsFile = File.createTempFile("allTaclets","tmp");
            PrintWriter out
                = new PrintWriter(new BufferedWriter(new FileWriter(allTacletsFile)));
            for (int i=0; i<ruleFiles.length; i++) {
                //File f = new File(ruleFiles[i]);
                File f = new File(KeYResourceManager.getManager().getResourceFile
                                  (CheckPrgTransfSoundness.class,
                                   ruleFiles[i]).getFile());
                BufferedReader r = new BufferedReader(new FileReader(f));
                for (String jl = r.readLine();(jl != null); jl = r.readLine()) {
                    if (!jl.startsWith("\\include")) out.println(jl);
                }
            }
            out.close();

            // KeYResourceManager.getManager().getResourceFile
            //            (CheckPrgTransfSoundness.class,  ruleFiles[i])
            EnvInput envInput = new KeYFileForTests("Test", allTacletsFile);
            ProblemInitializer pi = new ProblemInitializer(JAVA_PROFILE);
            InitConfig ic = pi.prepare(envInput);
            SetOfTaclet currentRules = ic.getTaclets();
            //filtern von currentRules mit obigen checkTacsName, treffer in rules hinzuf�gen
            // schleife �ber alle elemente von currentRules


            IteratorOfTaclet currentRulesIt = currentRules.iterator();
            while (currentRulesIt.hasNext()) {
                Taclet cT = (Taclet) currentRulesIt.next();

                Iterator checkTacsNameIt = checkTacsName.iterator();
                while (checkTacsNameIt.hasNext()) {
                    String tacName = (String) checkTacsNameIt.next();
                    if (cT.name().toString().equals(tacName)) {
                        rules=rules.add(cT);
                    }
                }
            }
        } catch (Exception e) {
            System.err.println("Exception occured while parsing "
                               +allTacletsFile+"\n");
                e.printStackTrace();
                System.exit(-1);
                return null;
        }


        return rules;

    }

    // This method iterates over all the taclets created by the parsing
    // process and feeds them to the "processTaclet" method.
    public static void processAllTaclets(SetOfTaclet taclets) {
        IteratorOfTaclet tacletIt = taclets.iterator();
        int i = 1;
        while(tacletIt.hasNext()) {
            Taclet tac = tacletIt.next();
            System.out.println(i + ". Taclet: "+tac.name());
            i++;
            processTaclet(tac);
            System.out.println();
        }
    }

    // This processes a taclet by using a lot of helper functions.
    public static void processTaclet(Taclet taclet) {
        // This first increases the counter for the tacletnumber and also
        // sets the case number back to 1, as this is another taclet to
        // be processed.
        currentTaclet = taclet;
        tacletCounter = tacletCounter + 1;
        caseCounter = 1;

        // This creates 2 new lines in the output file to separate this
        // taclet from the one before.
        try {
            fW.write("\n\n");
        }
        catch (Exception e) {
            System.err.println("Exception occured "
                               +"while writing to "+fW+"\n");
            e.printStackTrace();
            System.exit(-1);
            return;
        }

        // Extract all parts from the taclet and put them here:
        Term findTerm = null;
        Term replaceWithTerm = null;
        newvars = null;

        // Intermediate variable.
        ListOfTacletGoalTemplate listTgt = taclet.goalTemplates();

        if (taclet instanceof RewriteTaclet && listTgt.size() == 1) {
            findTerm = ((RewriteTaclet) taclet).find();
            replaceWithTerm =
                ((RewriteTacletGoalTemplate) listTgt.head())
                .replaceWith();
        }
        else {
            // Error: taclet has to be rewriteTaclet!
            // Error: either no goaltemplate available or more than 1.
            System.out.println("ERROR - taclet which is no "
                               +"RewriteTaclet or has no goalTemplate"
                               +"used: "+taclet);
        }

        // Set of new variable conditions:
        newvars = taclet.varsNew();

        // all parts, i.e. find, replacewith and newvarcond have now
        // been extracted, use them: first get inside the find part and
        // extract the information there by "preProcessFindPart"

        preProcessFindPart(findTerm);

        System.out.println("replacewith: "+replaceWithTerm);

        // Here we have a Map "svToRestriction" which maps all the
        // schema vars from "list" to a restriction class. This was
        // completed within the "preProcessFindPart". Using that
        // information we should now be able to create all the possible
        // mappings from sv's to concrete elements for the MJS.

        // Use method "createAllPossibilities" for the purpose of
        // creating *all* the possibilities.
        Set allSVSet = svToRestriction.keySet();
        int svarrsize = allSVSet.size();
        Object[] allSVs = allSVSet.toArray();
        Map svToMaude = new HashMap();
        createAllPossibilities(findTerm, replaceWithTerm, allSVs, 0,
                               svarrsize, new String(), svToMaude);

        // That is it for this method, return to here does not help.
    }

    // This method considers all code in the find part of the taclet and
    // checks it for necessary restrictions to the SVs.
    public static void preProcessFindPart(Term find) {
        System.out.println("find: " + find);

        // Extracts the StatementBlock of the find part.
        JavaBlock findJavaBlock = find.javaBlock();
        StatementBlock findStatementBlock
            = (StatementBlock) findJavaBlock.program();

        findStatementBlock = new StatementBlock(new StatementBlock(findStatementBlock.getBody()));

        // Collects all SVs in the code of the find part.
        ProgramSVCollector PSVC =
            new ProgramSVCollector(findStatementBlock,
                                   SLListOfSchemaVariable.EMPTY_LIST) ;
        PSVC.start();
        ListOfSchemaVariable list = PSVC.getSchemaVariables();

        // Creates a map with all the schema variables mapped to the no
        // restriction class.
        svToRestriction = new HashMap();
        IteratorOfSchemaVariable listIt = list.iterator();
        while (listIt.hasNext()) {
            svToRestriction.put(listIt.next(), RESTRICTNONE);
        }

        // going inside the statements, until terminalProgramElement
        // reached, "recurse"ing inside:
        for (int countStatements = 0;
             countStatements < findStatementBlock.getStatementCount();
             countStatements ++) {

            Statement findStatement =
                findStatementBlock.getStatementAt(countStatements);

            if (findStatement instanceof NonTerminalProgramElement) {
                //System.out.println("inside");
                recurse((NonTerminalProgramElement) findStatement, "",
                        RESTRICTNONE);
            }

        }

        // done here
    }

    // This method goes inside the statement which it is given and
    // extracts the restrictions.
    public static void recurse(NonTerminalProgramElement findStat,
                               String indent, Restriction restri) {
        for (int countst = 0 ;
             countst < findStat.getChildCount();
             countst ++) {

            ProgramElement findPE =
                findStat.getChildAt(countst);
            if (findPE instanceof NonTerminalProgramElement) {

                // In case of an arithmetic operator the SV has to have
                // integer type:
                if ((findPE instanceof Operator &&
                     TypeConverter.isArithmeticOperator((Operator)findPE))
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.PlusAssignment
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.MinusAssignment
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.TimesAssignment
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.DivideAssignment
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.ModuloAssignment
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.GreaterOrEquals
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.GreaterThan
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.LessOrEquals
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.LessThan
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.Equals
                    || findPE instanceof
                    de.uka.ilkd.key.java.expression.operator.NotEquals
                    ) {
                    // call recurse with a RestrictionInt, the current
                    // restriction should be either a RestrictionNone or
                    // a RestrictionInt, otherwise bad!

                    Restriction localRest = new RestrictionInt();

                    // Subcase of arithmetic operator where the
                    // restriction has to be bool, not int.
                    if (findPE instanceof
                        de.uka.ilkd.key.java.expression.operator.BinaryAnd
                        || findPE instanceof
                        de.uka.ilkd.key.java.expression.operator.BinaryNot
                        || findPE instanceof
                        de.uka.ilkd.key.java.expression.operator.BinaryOr
                        || findPE instanceof
                        de.uka.ilkd.key.java.expression.operator.BinaryXOr) {
                        localRest = new RestrictionBool();
                    }

                    // Go on with the recursion.
                    if (((NonTerminalProgramElement) findPE)
                        .getChildCount() == 0) {
                        finishRecurse((NonTerminalProgramElement) findPE,
                                      indent+" ", localRest);
                    }
                    else {
                        recurse((NonTerminalProgramElement) findPE,
                                indent+" ", localRest);
                    }
                }

                else if (findPE instanceof
                         de.uka.ilkd.key.java.reference
                         .SchematicFieldReference) {
                    // call recurse (or finish the recursion) with a
                    // RestrictionAtt which has the second child as
                    // parameter, i.e. we have "e.a" and "e" gets the
                    // RestrictionAtt(a) and "a" gets the restriction
                    // which is there from a higher level of the
                    // recursion in addition to the restriction of being
                    // an attribute. For "a" the recursion is finished.

                    NonTerminalProgramElement child0 =
                        (NonTerminalProgramElement)
                        ((NonTerminalProgramElement) findPE).getChildAt(0);
                    NonTerminalProgramElement child1 =
                        (NonTerminalProgramElement)
                        ((NonTerminalProgramElement) findPE).getChildAt(1);

                    if (child0.getChildCount() == 0) {
                        finishRecurse (child0, indent+" ",
                                       new RestrictionAtt(((SchemaVariable)
                                                           child1)));
                    }
                    else {
                        recurse(child0, indent+" ",
                                new RestrictionAtt(((SchemaVariable)
                                                    child1)));
                    }

                    finishRecurse(child1, indent+" ",
                                  new RestrictionIsAttrib(restri));
                }
                else {
                    // this is the standard base case when no
                    // restriction needs to be set due to the current
                    // operator

                    if (((NonTerminalProgramElement) findPE)
                        .getChildCount() == 0) {
                        finishRecurse((NonTerminalProgramElement) findPE,
                                      indent+" ", restri);
                    }
                    else
                    {
                        recurse((NonTerminalProgramElement) findPE,
                                indent+" ", restri);
                    }
                }
            }
            else{
                System.out.println("terminal found: " +
                                   ((NonTerminalProgramElement) findStat)
                                   .getChildAt(countst));
                System.out.println("this should not have happened, all "
                                   + "things we get by accessing "
                                   + "these children are of NTPE type");
            }
        }
    }

    // This method ends the recursion.
    public static void finishRecurse(NonTerminalProgramElement findStat,
                                     String indent, Restriction restri) {
        if (findStat instanceof TerminalProgramElement) {

            if (findStat instanceof SchemaVariable) {

                // Here we are at the bottom level, having a single
                // schema variable left, we now assign to that sv a
                // restriction globally for this taclet. This might be
                // overwritten, but that will only happen with another
                // copy of itself.

                if (restri instanceof RestrictionNone) {
                    // No change at the sv to restriction mapping. There
                    // is no need for a change due to this leaf of the
                    // parse tree because the current restriction is
                    // RestrictionNone, but there might be a restriction
                    // already due to another leaf which can not be
                    // overwritten just because here this is not
                    // necessary.
                }
                else {
                    // We have a restriction on the sv here, just put it
                    // into the mapping. It could overwrite another one
                    // already there but as we only consider
                    // parse-correct taclets this should not bother
                    // us. Also in the taclets we consider every
                    // dereferencing that appears will only appear with
                    // the left-hand side used with the same attribute
                    // again, so there is no problem with one attribute
                    // overwriting another.
                    svToRestriction.put(findStat, restri);
                }

            }
        }
    }

    // This method splits the generation up into all possible parts
    // which are induced by the SVs. That happens by repeatedly calling
    // itself with ever more parts specified.
    public static void
        createAllPossibilities(Term find, Term replaceWith,
                               Object[] allSVs, int svarrindex, int svarrsize,
                               String addString, Map svToMaude) {

        if (svarrindex < svarrsize) {
            SchemaVariable sv = (SchemaVariable) allSVs[svarrindex];
            svarrindex = svarrindex + 1;
            Restriction svRestri = (Restriction) svToRestriction.get(sv);

            Sort svSort = ((SortedSchemaVariable) sv).sort();

            // Here we find out the type and restrictions for each
            // schema variable and accordingly create all subcases. We
            // save the current case in the form of a map from SVs to
            // the fixed strings from above, like AttribVal,
            // AttribInt,...

            // We also generate the "add" part for the Maude
            // configuration for each SV, they get collected into the
            // "addstring" string.

            // Then the method is called again to fix the cases of the
            // remaining SVs.

            // This is the name of the current SV, without the "#" in
            // the name as usual in KeY because Maude cannot use it that
            // way.
            String svName = sv.name().toString()
                .substring(1,sv.name().toString().length());
            // This string is added to the recursive call to this
            // method, thus it starts out empty.
            String addNow = "";

            // Case distinctions depending on the SV sort and the
            // restriction, in each case one (or more!) subcases are
            // opened with a recursive call to the current method and
            // the case of the current SV is saved in svToMaude and put
            // into the string.

            if (svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.VARIABLE
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.LEFTHANDSIDE
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.NONSIMPLEEXPRESSION
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.EXPRESSION) {
                if (svRestri instanceof RestrictionIsAttrib) {
                    Restriction attribsRestri =
                        ((RestrictionIsAttrib) svRestri)
                        .getAttribsRestriction();
                    if (attribsRestri instanceof RestrictionNone) {
                        addNow = createStringMemoryVal(svName);
                        svToMaude.put(sv, ATTRIBVAL);
                    }
                    else if (attribsRestri instanceof RestrictionInt) {
                        addNow = createStringMemoryInt(svName);
                        svToMaude.put(sv, ATTRIBINT);
                    }
                    else if (attribsRestri instanceof RestrictionBool) {
                        addNow = createStringMemoryBool(svName);
                        svToMaude.put(sv, ATTRIBBOOL);
                    }
                    else {
                        // Bad Case, this means that the attribute is
                        // restricted to have an attribute which cannot
                        // happen!
                        System.out.println("Bad Case! This is an attribute "
                                           +"which can not have another "
                                           +"attribute, but needs one.");
                    }
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                if (svRestri instanceof RestrictionNone) {
                    // 1. : sv is local variable!
                    addNow =
                        createStringLocalEnv(svName)
                        + createStringMemoryVal(svName);
                    svToMaude.put(sv, LOCALVARVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 2. : sv is attribute of the current object w/out "this"
                    // ATTOBJWOTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryVal(svName);
                    svToMaude.put(sv, ATTOBJWOTHISVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 3. : sv is attribute of the current object w/ "this"
                    //ATTOBJWITHTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryVal(svName);
                    svToMaude.put(sv, ATTOBJWOTHISVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionInt) {

                    // 1. : sv is local variable!
                    addNow =
                        createStringLocalEnv(svName)
                        + createStringMemoryInt(svName);
                    svToMaude.put(sv, LOCALVARINT );
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 2. : sv is attribute of the current object w/out "this"
                    // ATTOBJWOTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryInt(svName);
                    svToMaude.put(sv, ATTOBJWOTHISINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 3. : sv is attribute of the current object w/ "this"
                    //ATTOBJWITHTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryInt(svName);
                    svToMaude.put(sv, ATTOBJWITHTHISINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionBool) {

                    // 1. : sv is local variable!
                    addNow =
                        createStringLocalEnv(svName)
                        + createStringMemoryBool(svName);
                    svToMaude.put(sv, LOCALVARBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 2. : sv is attribute of the current object w/out "this"
                    // ATTOBJWOTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryBool(svName);
                    svToMaude.put(sv, ATTOBJWOTHISBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 3. : sv is attribute of the current object w/ "this"
                    //ATTOBJWITHTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryBool(svName);
                    svToMaude.put(sv, ATTOBJWITHTHISBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionAtt) {
                    String svAttName =
                        svRestri.getAttributeVar().name().toString()
                        .substring(1,svRestri.getAttributeVar().name()
                                   .toString().length());

                    // 1. : sv is local variable!
                    addNow =
                        createStringLocalEnv(svName)
                        + createStringMemoryObjWAtt(svName, svAttName);
                    svToMaude.put(sv, LOCALVARATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 2. : sv is attribute of the current object w/out "this"
                    // ATTOBJWOTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryObjWAtt(svName, svAttName);
                    svToMaude.put(sv, ATTOBJWOTHISATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 3. : sv is attribute of the current object w/ "this"
                    //ATTOBJWITHTHIS
                    addNow =
                        createStringCurrObjEnv(svName)
                        + createStringMemoryObjWAtt(svName, svAttName);
                    svToMaude.put(sv, ATTOBJWITHTHISATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionIsAttrib) {

                }
                else {
                    System.out.println("Problem, all cases are worked on so "
                                       +"this should not be reachable!");
                }
            }

            if (svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.STATICVARIABLE
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.LEFTHANDSIDE
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.NONSIMPLEEXPRESSION
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.EXPRESSION) {
                if (svRestri instanceof RestrictionNone) {
                    // 1. : sv is static attribute with STATATTTYPEREF !
                    // I.e. type reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryVal(svName);
                    svToMaude.put(sv, STATATTTYPEREFVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                    // 2. : sv is static attribute with STATATTOBJREF!
                    // I.e. object reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryVal(svName)
                        + createStringLocalEnv(svName+"ObjRef")
                        + createStringMemoryObj(svName);
                    svToMaude.put(sv, STATATTOBJREFVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                }
                else if (svRestri instanceof RestrictionInt) {

                    // 1. : sv is static attribute with STATATTTYPEREF !
                    // I.e. type reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryInt(svName);
                    svToMaude.put(sv, STATATTTYPEREFINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                    // 2. : sv is static attribute with STATATTOBJREF!
                    // I.e. object reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryInt(svName)
                        + createStringLocalEnv(svName+"ObjRef")
                        + createStringMemoryObj(svName);
                    svToMaude.put(sv, STATATTOBJREFINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                }
                else if (svRestri instanceof RestrictionBool) {

                    // 1. : sv is static attribute with STATATTTYPEREF !
                    // I.e. type reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryBool(svName);
                    svToMaude.put(sv, STATATTTYPEREFBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                    // 2. : sv is static attribute with STATATTOBJREF!
                    // I.e. object reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryBool(svName)
                        + createStringLocalEnv(svName+"ObjRef")
                        + createStringMemoryObj(svName);
                    svToMaude.put(sv, STATATTOBJREFBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);

                }
                else if (svRestri instanceof RestrictionAtt) {
                    String svAttName =
                        svRestri.getAttributeVar().name().toString()
                        .substring(1,svRestri.getAttributeVar().name()
                                   .toString().length());
                    // 1. : sv is static attribute with STATATTTYPEREF !
                    // I.e. type reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryObjWAtt(svName, svAttName);
                    svToMaude.put(sv, STATATTTYPEREFATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                    // 2. : sv is static attribute with STATATTOBJREF!
                    // I.e. object reference first
                    addNow =
                        createStringStaticEnv(svName)
                        + createStringMemoryObjWAtt(svName, svAttName)
                        + createStringLocalEnv(svName+"ObjRef")
                        + createStringMemoryObj(svName);
                    svToMaude.put(sv, STATATTOBJREFATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else {
                    System.out.println("Problem, all cases are worked on so "
                                       +"this should not be reachable!");
                }
            }

            if (svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.SIMPLEEXPRESSION
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.EXPRESSION) {
                // see also above, this shares a case with VARIABLE
                if (svRestri instanceof RestrictionNone) {
                    addNow = "";
                    svToMaude.put(sv, LITERALVALUE);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionInt) {
                    addNow = "";
                    svToMaude.put(sv, LITERALINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionBool) {
                    addNow = "";
                    svToMaude.put(sv, LITERALBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionAtt) {
                    // This case can not happen for variables and
                    // lefthandsides, therefore nothing is done
                    // here. For (nonsimple) expressions this case is
                    // handled further down!

                    // It actually can not happen as a literal,
                    // i.e. there can not be an "object literal" which
                    // makes this case moot!
                }
                else {
                    System.out.println("Problem, all cases are worked on so "
                                       +"this should not be reachable!");
                }
            }

            if (svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.NONSIMPLEEXPRESSION
                || svSort ==
                de.uka.ilkd.key.logic.sort.ProgramSVSort.EXPRESSION) {
                // for more on these cases take a look above at the
                // variable, static variable and simple expression
                // cases.

                // nothing needs to be put into the memory here,
                // i.e. into the addNow string, here an expression is
                // going to be evaluated!
                if (svRestri instanceof RestrictionNone) {
                    addNow = "";
                    svToMaude.put(sv, EXPRESSIONVAL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionInt) {
                    addNow = "";
                    svToMaude.put(sv, EXPRESSIONINT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionBool) {
                    addNow = "";
                    svToMaude.put(sv, EXPRESSIONBOOL);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else if (svRestri instanceof RestrictionAtt) {
                    addNow = "";
                    svToMaude.put(sv, EXPRESSIONATT);
                    createAllPossibilities(find, replaceWith, allSVs,
                                           svarrindex, svarrsize,
                                           addString+addNow, svToMaude);
                }
                else {
                    System.out.println("Problem, all cases are worked on so "
                                        +"this should not be reachable!");
                }
            }


        }
        else {
            // this is the first (and only) call to
            // "createAllPossibilities" with the iterator used up and
            // thus all schemavariables have been assigned
            // something. now it is time to assign the fitting add for
            // the find part and afterwards the code for that find part;
            // then check the newvars, do the assignment there, then
            // create the add-new and the code string for the
            // replacewith part. All this in done in the extra methods
            // below.

            // These 3 strings are class attributes, reset all of them
            // to the empty string as they might have been used before
            findString = new String();
            replaceWithString = new String();
            addNewString = new String();

            // this adds a mapping from the new vars to their maude
            // meanings into the var to maude meaning mappings!
            createNewVarsAddString(svToMaude);
            //System.out.println("addNewString here: "+addNewString);

            createFindCode(find, svToMaude);
            createReplaceWithCode(replaceWith, svToMaude);
            putStringTogetherWriteToFile(addString, svToMaude);
        }
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringLocalEnv(String svName) {
        return
            "addToLocalEnv("
            +svName+"Name:Name, "
            +svName+"Loc:Location) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringCurrObjEnv(String svName) {
        return
            "addToCurrentObjEnv("
            +svName+"Name:Name, "
            +svName+"Loc:Location) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringStaticEnv(String svName) {
        return
            "addToStaticEnv("
            +svName+"CT:CType, "
            +svName+"Name:Name, "
            +svName+"Loc:Location) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringMemoryVal(String svName) {
        return
            "addToMemory("
            +svName+"Loc:Location, "
            +svName+"Val:Value) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringMemoryInt(String svName) {
        return
            "addToMemory("
            +svName+"Loc:Location, "
            + "int("
            +svName+"Val:Int)"
            +") ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringMemoryBool(String svName) {
        return
            "addToMemory("
            +svName+"Loc:Location, "
            + "bool("
            +svName+"Val:Bool)"
            +") ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringMemoryObj(String svName) {
        return
            "addToMemory("
            +svName+"ObjRef"+"Loc:Location, "
            +"o("
            +svName+"CT:CType, "
            +svName+"CT:CType, "
            +svName+"ObjEnv:ObjEnv)) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringMemoryObjWAtt(String svName,
                                                   String svAttName) {
        return
            "addToMemory("
            +svName+"Loc:Location, "
            +"o("
            +svName+"CT:CType, "
            +svName+"CT:CType, "
            +svName+"ObjEnv:ObjEnv "
            +"("+svName+"CT:CType, ["+svAttName+"Name:Name, "
            +svAttName+"Loc:Location]))) ";
    }


    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringNewVarVal(String svName) {
        return
            "addNewToLocalEnvAndMem("
            +svName+"Name:TacletNewVarName, "
            +svName+"Loc:TacletNewLocation, "
            +svName+"Val:Value) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringNewVarInt(String svName) {
        return
            "addNewToLocalEnvAndMem("
            +svName+"Name:TacletNewVarName, "
            +svName+"Loc:TacletNewLocation, "
            +"int("+svName+"Val:Int)) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringNewVarBool(String svName) {
        return
            "addNewToLocalEnvAndMem("
            +svName+"Name:TacletNewVarName, "
            +svName+"Loc:TacletNewLocation, "
            +"bool("+svName+"Val:Bool)) ";
    }

    // Method to create a String which can be put into a Maude "add..."
    // part.
    public static String createStringNewVarAtt(String svName,
                                               String svPeerName) {
        return
            "addNewToLocalEnvAndMem("
            +svName+"Name:TacletNewVarName, "
            +svName+"Loc:TacletNewLocation, "
            +"o("
            +svPeerName+"CT:CType, "
            +svPeerName+"CT:CType, "
            +svPeerName+"ObjEnv:ObjEnv)) ";
    }


    // In this method the new variables are assigned to their
    // maude-"values", the result of this is the side effect on
    // "addNewString"
    public static void createNewVarsAddString(Map svToMaude) {
        addNewString = "";
        IteratorOfNewVarcond newvarsIt = newvars.iterator();
        while (newvarsIt.hasNext()) {
            NewVarcond newVC =  newvarsIt.next();
            SchemaVariable sv = newVC.getSchemaVariable();
            SchemaVariable svPeer = newVC.getPeerSchemaVariable();
            Sort svPeerSort = ((SortedSchemaVariable) svPeer).sort();
            String svMaudeCase = (String) svToMaude.get(svPeer);

            // New SV's name.
            String svName = sv.name().toString()
                .substring(1,sv.name().toString().length());
            // Name of the SV which gives its type to the current new
            // SV.
            String svPeerName = svPeer.name().toString()
                .substring(1,svPeer.name().toString().length());

            // Case for the new SV is stored in svToMaude.
            svToMaude.put(sv, svMaudeCase);

            // Depending on the case the add-String is extended.
            if (svMaudeCase == LOCALVARVAL
                || svMaudeCase == ATTOBJWOTHISVAL
                || svMaudeCase == ATTOBJWITHTHISVAL
                || svMaudeCase == STATATTTYPEREFVAL
                || svMaudeCase == STATATTOBJREFVAL
                || svMaudeCase == LITERALVALUE
                || svMaudeCase == EXPRESSIONVAL
                || svMaudeCase == ATTRIBVAL) {
                addNewString = addNewString
                    + createStringNewVarVal(svName);
            }
            else if (svMaudeCase == LOCALVARINT
                     || svMaudeCase == ATTOBJWOTHISINT
                     || svMaudeCase == ATTOBJWITHTHISINT
                     || svMaudeCase == STATATTTYPEREFINT
                     || svMaudeCase == STATATTOBJREFINT
                     || svMaudeCase == LITERALINT
                     || svMaudeCase == EXPRESSIONINT
                     || svMaudeCase == ATTRIBINT) {
                addNewString = addNewString
                    + createStringNewVarInt(svName);
            }
            else if (svMaudeCase == LOCALVARBOOL
                     || svMaudeCase == ATTOBJWOTHISBOOL
                     || svMaudeCase == ATTOBJWITHTHISBOOL
                     || svMaudeCase == STATATTTYPEREFBOOL
                     || svMaudeCase == STATATTOBJREFBOOL
                     || svMaudeCase == LITERALBOOL
                     || svMaudeCase == EXPRESSIONBOOL
                     || svMaudeCase == ATTRIBBOOL) {
                addNewString = addNewString
                    + createStringNewVarBool(svName);
            }
            else if (svMaudeCase == LOCALVARATT
                     || svMaudeCase == ATTOBJWOTHISATT
                     || svMaudeCase == ATTOBJWITHTHISATT
                     || svMaudeCase == STATATTTYPEREFATT
                     || svMaudeCase == STATATTOBJREFATT
                     || svMaudeCase == EXPRESSIONATT) {
                addNewString = addNewString
                    + createStringNewVarAtt(svName, svPeerName);
            }
        }
    }

    // This method creates the code for the find part. It is stored in
    // the static findString attribute.
    public static void createFindCode(Term find, Map svToMaude) {
        JavaBlock findJavaBlock = find.javaBlock();

        StatementBlock findStatementBlock =
            (StatementBlock) findJavaBlock.program();

        if (findStatementBlock == null
            || findStatementBlock.getStatementCount() == 0) {
            // the code is empty
            findString = findString + "";
            return ;
        }

        Statement findStatement = new StatementBlock(findStatementBlock.getBody());

        // Transform every statement.
        for (int countStatements = 0;
             countStatements <
                 ((NonTerminalProgramElement) findStatementBlock)
                 .getChildCount();
             countStatements ++) {

            ProgramElement findPE =
                ((NonTerminalProgramElement) findStatement)
                .getChildAt(countStatements);

            // Add the current statement to the Maude code with the help
            // of the recursion.
            findString = findString + recurseFindRepl(findPE, svToMaude) +" ; ";


        }

    }

    // This works the same way as in the find part case,
    // i.e. "createFindCode" but writes into replaceWithString as
    // result.
    public static void createReplaceWithCode(Term replaceWith, Map svToMaude) {
        JavaBlock replaceWithJavaBlock = replaceWith.javaBlock();

        StatementBlock replaceWithStatementBlock =
            (StatementBlock) replaceWithJavaBlock.program();

        if (replaceWithStatementBlock == null
            || replaceWithStatementBlock.getStatementCount() == 0) {
            // the code is empty
            replaceWithString = replaceWithString + "";
            return ;
        }

        Statement replaceWithStatement
           = new StatementBlock( replaceWithStatementBlock.getBody());

        for (int countStatements = 0;
             countStatements <
                 ((NonTerminalProgramElement) replaceWithStatement)
                 .getChildCount();
             countStatements ++) {

            ProgramElement replaceWithPE =
                ((NonTerminalProgramElement) replaceWithStatement)
                .getChildAt(countStatements);

            replaceWithString = replaceWithString +
                recurseFindRepl(replaceWithPE, svToMaude) +" ; ";


        }
    }

    // This is the actual core of both "createFindCode" and
    // "createReplaceWithCode" methods. It puts the parts together by
    // recursing in the subparts of each operator.
    public static String recurseFindRepl(ProgramElement pE, Map svToMaude) {
        String result1;
        String result2;
        if (pE instanceof NonTerminalProgramElement
            && ((NonTerminalProgramElement) pE).getChildCount() == 0
            && pE instanceof SchemaVariable) {

            SchemaVariable sv = (SchemaVariable) pE;

            String svName = sv.name().toString()
                .substring(1,sv.name().toString().length());

            String svMaudeCase = (String) svToMaude.get(sv);

            // in case the current sv is one of the "new schema vars"
            // that sv is replaced in the code by
            // sv+"Name:TacletNewVarName" and it does not matter what
            // the type of the variable is!
            IteratorOfNewVarcond newvarsIt = newvars.iterator();
            while (newvarsIt.hasNext()) {
                NewVarcond newVC = newvarsIt.next();
                SchemaVariable newSV = newVC.getSchemaVariable();
                if (sv == newSV) {
                    return svName+"Name:TacletNewVarName";
                }
            }

            // Reaching this code we know that the sv is not a "new"
            // one. So we need to distinguish the "types".
            if (svMaudeCase == ATTRIBVAL
                || svMaudeCase == ATTRIBINT
                || svMaudeCase == ATTRIBBOOL) {
                return svName+"Name:Name";
            }
            if (svMaudeCase == LOCALVARVAL
                || svMaudeCase == LOCALVARINT
                || svMaudeCase == LOCALVARBOOL
                || svMaudeCase == LOCALVARATT
                || svMaudeCase == ATTOBJWOTHISVAL
                || svMaudeCase == ATTOBJWOTHISINT
                || svMaudeCase == ATTOBJWOTHISBOOL
                || svMaudeCase == ATTOBJWOTHISATT) {
                return svName+"Name:Name";
            }
            if (svMaudeCase == ATTOBJWITHTHISVAL
                || svMaudeCase == ATTOBJWITHTHISINT
                || svMaudeCase == ATTOBJWITHTHISBOOL
                || svMaudeCase == ATTOBJWITHTHISATT) {
                return "(this . "+svName+"Name:Name)";
            }
            if (svMaudeCase == STATATTTYPEREFVAL
                || svMaudeCase == STATATTTYPEREFINT
                || svMaudeCase == STATATTTYPEREFBOOL
                || svMaudeCase == STATATTTYPEREFATT) {
                return "("+svName+"CT:CType . "+svName+"Name:Name)";
            }
            if (svMaudeCase == STATATTOBJREFVAL
                || svMaudeCase == STATATTOBJREFINT
                || svMaudeCase == STATATTOBJREFBOOL
                || svMaudeCase == STATATTOBJREFATT) {
                return "("+svName+"ObjRefName:Name . "+svName+"Name:Name)";
                }
            if (svMaudeCase == LITERALINT) {
                return "#i("+svName+"Val:Int)";
            }
            if (svMaudeCase == LITERALBOOL) {
                return "#b("+svName+"Val:Bool)";
            }
            if (svMaudeCase == LITERALVALUE) {
                return "resIsValue("+svName+"Val:Value)";
            }
            if (svMaudeCase == EXPRESSIONVAL) {
                return "eval("+svName+"EN:ExpressionName , "
                    +"non-primitive-result)";
            }
            if (svMaudeCase == EXPRESSIONINT) {
                return "eval("+svName+"EN:ExpressionName , int-result)";
            }
            if (svMaudeCase == EXPRESSIONBOOL) {
                return "eval("+svName+"EN:ExpressionName , bool-result)";
            }
            if (svMaudeCase == EXPRESSIONATT) {
                if (sv instanceof SortedSchemaVariable) {
                    // It is clear from above that the "sv" is not a
                    // "new sv" and therefore there is an entry for this
                    // "sv" in the svToRestriction map, which would not
                    // be the case for a "new schema var".
                    Sort svSort = ((SortedSchemaVariable) sv).sort();
                    RestrictionAtt restri =
                        (RestrictionAtt) svToRestriction.get(sv);
                    SchemaVariable svAtt = restri.getAttributeVar();
                    String svAttName = svAtt.name().toString()
                        .substring(1,svAtt.name().toString().length());
                    Restriction attRestri =
                        ((RestrictionIsAttrib)
                         ((Restriction) svToRestriction.get(svAtt)))
                        .getAttribsRestriction();
                    String primitiveExpressionResultType = "";
                    if (attRestri instanceof RestrictionNone) {
                        primitiveExpressionResultType = "non-primitive-result";
                    }
                    else if (attRestri instanceof RestrictionInt) {
                        primitiveExpressionResultType = "int-result";
                    }
                    else if (attRestri instanceof RestrictionBool) {
                        primitiveExpressionResultType = "bool-result";
                    }
                    else {
                        System.out.println("Problem, das h�tte andere "
                                           +"Restriction haben m�ssen");
                    }
                    return
                        "eval("+svName+"EN:ExpressionName , obj-result("
                        +svName+"CT:CType , "+ svAttName+"Name:Name , "
                        + primitiveExpressionResultType   +"))";
                }
                else {
                    System.out.println("Problem, dies sollte immer eine "
                                       +"SortedSchemaVariable sein!");
                }
            }

            return "ERROR!";

        }
        else if (pE instanceof TerminalProgramElement ) {
            // This only works as long as all considered literals are
            // ints! If other literals are allowed that needs to be
            // tested and treated accordingly.
            return "#i("+pE.toString()+")";
        }
        else if (pE instanceof NonTerminalProgramElement
                  && ((NonTerminalProgramElement) pE).getChildCount() == 1) {
            result1 = recurseFindRepl(((NonTerminalProgramElement) pE)
                                      .getChildAt(0), svToMaude);
            // The result is used with the current operator in each
            // case.
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.PreIncrement) {
                return "++ " + result1;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.PostIncrement) {
                return result1 + " ++";
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.PreDecrement) {
                return "-- " + result1;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.PostDecrement) {
                return result1 + " --";
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.ParenthesizedExpression) {
                //System.out.println(pE);
                return "("+result1+")";
            }
            if (pE instanceof
                de.uka.ilkd.key.java.declaration.VariableSpecification) {
                return result1;
            }
            if (pE instanceof de.uka.ilkd.key.rule.metaconstruct.TypeOf) {

                // for now we just return an empty string and do not
                // care about the type this should yield
                return "";
            }
            System.out.println("This is an untreated 1-argument case: ");
            System.out.println("PE: "+pE+" TYPE: "+pE.getClass() );

        }
        else if (pE instanceof NonTerminalProgramElement
                  && ((NonTerminalProgramElement) pE).getChildCount() == 2) {
            result1 = recurseFindRepl(((NonTerminalProgramElement) pE)
                                      .getChildAt(0), svToMaude);
            result2 = recurseFindRepl(((NonTerminalProgramElement) pE)
                                      .getChildAt(1), svToMaude);
            // Result strings are used together with the current
            // operator to get the "total result".
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.CopyAssignment) {
                return result1 +" = "+ result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.TypeCast) {
                // RESTRICTED ONLY!
                // as with "TypeOf" this for now only yields an empty
                // string instead of {type} and thus only returns the
                // second argument basically! (so here instead of
                // "{result1} result2" this only gives "result2" because
                // the "result1" is empty!
                return "" + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.declaration.LocalVariableDeclaration) {
                // CORRECT -- RESTRICTED ONLY DUE to "TypeOf"!  The
                // first result is going to be from "TypeOf" and thus
                // will be the empty string. We leave it in here so that
                // if "TypeOf" is fixed, this is ok too. But for the
                // meantime this might end up not declaring something
                // new but just be the second result.  No real
                // restriction here!
                return result1 + " " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Plus) {
                return result1 + " + " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Minus) {
                return result1 + " - " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Times) {
                return result1 + " * " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Divide) {
                return result1 + " / " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Modulo) {
                return result1 + " % " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.PlusAssignment) {
                return result1 + " += " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.MinusAssignment) {
                return result1 + " -= " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.TimesAssignment) {
                return result1 + " *= " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.DivideAssignment) {
                return result1 + " /= " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.ModuloAssignment) {
                return result1 + " %= " + result2;
            }

            if (pE instanceof de.uka.ilkd.key.java.expression.operator.Equals) {
                return result1 + " == " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.NotEquals) {
                return result1 + " != " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.LessThan) {
                return result1 + " < " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.LessOrEquals) {
                return result1 + " <= " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.GreaterThan) {
                return result1 + " > " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.GreaterOrEquals) {
                return result1 + " >= " + result2;
            }

            // binary and
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.BinaryAnd) {
                return result1 +" && "+ result2;
            }
            // binary or
            if (pE instanceof
                de.uka.ilkd.key.java.expression.operator.BinaryOr) {
                return result1 +" || "+ result2;
            }

            if (pE instanceof
                de.uka.ilkd.key.java.declaration.VariableSpecification) {
                return result1 + " = " + result2;
            }
            if (pE instanceof
                de.uka.ilkd.key.java.reference.SchematicFieldReference) {
                return result1 + " . " + result2;
            }
            if (pE instanceof de.uka.ilkd.key.java.reference.ArrayReference) {
                return result1 + " [ " + result2 + " ]";
            }
            System.out.println("This is an untreated 2-argument case: ");
            System.out.println("PE: "+pE+" TYPE: "+pE.getClass() );
        }
        else {
            // Bad, should not happen
            System.out.println("Problem! This should not happen!");
        }

        return "";
    }

    // This method puts the whole string together from the parts created
    // before. See the Maude interface to see why the string is built as
    // below.
    public static void putStringTogetherWriteToFile(String addString,
                                                    Map svToMaude) {
        String resultString =
            "compareResultsModNewVars(\n"
            +"add(basicInitConfiguration, \n"
            + "    "+ addString + ", \n"
            + "    "+"("+findString+").BlockStatements"+ " -> endOfInitCode\n"
            + "   "+"), \n"
            +"add(basicInitConfiguration,  \n"
            + "    "+ addString + " " + addNewString + ", \n"
            + "    "+"("+ replaceWithString+").BlockStatements"
            + " -> endOfInitCode\n"
            + "   "+")) ";

        resultString = "search in PGM-SEMANTICS :  caseInfo("+ tacletCounter +", "+ caseCounter
            +", " + resultString + ")  =>! ResultingBoolVal:[Bool] .  \n\n";

        String infoString =
            "---- tacletnumber: "+tacletCounter+", casenumber: "
            + caseCounter +"\n"
            +"---- tacletname: " +currentTaclet.displayName() +" \n"
            +"---- case for each SV: \n";

        Set allSVs = svToMaude.keySet();
        Iterator allSVsIt = allSVs.iterator();
        while (allSVsIt.hasNext()) {
            SchemaVariable sv = (SchemaVariable) allSVsIt.next();
            String svCase = (String) svToMaude.get(sv);
            infoString = infoString + "---- SV: "+ sv +", Case:"
                + svCase + " \n";
        }

        try {
            fW.write(infoString+resultString);
        }
        catch (Exception e) {
            System.err.println("Exception occured while writing to "+fW+"\n");
            e.printStackTrace();
            System.exit(-1);
            return;
        }

        caseCounter = caseCounter + 1;
    }

    // Main method which starts everything.
    public static void main(String args[]) {
        try {
            // First overwrite the given file to make it empty,
            fW = new FileWriter(args[0], false);
            fW.write("");
            fW.close();
            // then open it and append everything which follows.
            fW = new FileWriter(args[0], true);
        }
        catch (Exception e) {
            System.err.println("Exception occured while opening file "+fW+"\n");
            e.printStackTrace();
            System.exit(-1);
            return;
        }

        SetOfTaclet taclets = parseTaclets();
        processAllTaclets(taclets);

        try {
            fW.close();
        }
        catch (Exception e) {
            System.err.println("Exception occured while closing file "+fW+"\n");
            e.printStackTrace();
            System.exit(-1);
            return;
        }
    }

}

