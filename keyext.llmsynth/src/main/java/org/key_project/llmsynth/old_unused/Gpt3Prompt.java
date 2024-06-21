package org.key_project.llmsynth.old_unused;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.theokanning.openai.service.OpenAiService;
import com.theokanning.openai.completion.chat.*;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import io.reactivex.Flowable;
import org.key_project.llmsynth.UnclosedProof;
import org.key_project.llmsynth.jml.JmlHelper;
import org.key_project.llmsynth.jml.ParsingException;
import org.key_project.util.collection.ImmutableList;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class Gpt3Prompt {
    //region Literals
    final static String STR_NEXT_QUERY =
            "===================== NEXT QUERY =====================";
    final static String STR_INIT_QUERY =
            "==================== INITIAL QUERY ====================";
    final static String STR_QUERY_RESPONSE =
            "====================== RESPONSE ======================";
    final static String STR_ABORT =
            "====================== ABORTING ======================";
    final static String STR_SUCCESS =
            "======================= SUCCESS =======================";
    final static String STR_PROCESSING =
            "================= POCESSING RESPONSE =================";
    final static String BOT_DESCRIPTION_OLD =
            "You are a system that helps to write Java Modeling Language (JML).\n" +
            "When prompted, you will add JML-code to a given class such that it specifies the behaviour of selected methods inside.";
    final static String BOT_DESCRIPTION = "You are a system that helps to write Java Modeling Language (JML)\n" +
            "When prompted, you will add JML-code to a given class such that it specifies the behaviour of selected methods inside.\n" +
            "You only answer with the code of JML contracts.\n" +
            "You do not describe what you do.\n" +
            "You do not describe the methods.\n" +
            "You do not add commentary strings.";
    final static ChatMessage systemMessage = new ChatMessage(ChatMessageRole.SYSTEM.value(), BOT_DESCRIPTION);

    //final static String PTN_METHOD_OLD = "(public|protected|private|static|\\s) +[\\w\\<\\>\\[\\],\\s]+\\s+(\\w+) *\\([^\\)]*\\) *(\\{?|[^;])";
    final static String PTN_METHOD_OLD = "(public|protected|private|static) +[\\w\\<\\>\\[\\],\\s]+\\s+(\\w+) *\\([^\\)]*\\) *(\\{?|[^;])";
    final static String PTN_METHOD = "^[ \\t]*(?:(?:public|protected|private)\\s+)?(?:(static|final|native|synchronized|abstract|threadsafe|transient|(?:<[?\\w\\[\\] ,&]+>)|(?:<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>[^>]*>))\\s+){0,}(?!return)\\b([\\w.]+)\\b(?:|(?:<[?\\w\\[\\] ,&]+>)|(?:<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>[^>]*>))((?:\\[\\]){0,})\\s+\\b\\w+\\b\\s*\\(\\s*(?:\\b([\\w.]+)\\b(?:|(?:<[?\\w\\[\\] ,&]+>)|(?:<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>[^>]*>))((?:\\[\\]){0,})(\\.\\.\\.)?\\s+(\\w+)\\b(?![>\\[])\\s*(?:,\\s+\\b([\\w.]+)\\b(?:|(?:<[?\\w\\[\\] ,&]+>)|(?:<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>)|(?:<[^<]*<[^<]*<[?\\w\\[\\] ,&]+>[^>]*>[^>]*>))((?:\\[\\]){0,})(\\.\\.\\.)?\\s+(\\w+)\\b(?![>\\[])\\s*){0,})?\\s*\\)(?:\\s*throws [\\w.]+(\\s*,\\s*[\\w.]+))?\\s*(?:\\{|;)[ \\t]*$";

    final static String PTN_JML = "@";
    final static Pattern method_decl = Pattern.compile(PTN_METHOD_OLD);
    final static Pattern method_jml = Pattern.compile(PTN_JML);
    final static Pattern gpt_code_delim = Pattern.compile("```");

    //endregion

    public static boolean verbose = true;
    public static void status(String msg) {
        if (verbose)
            System.out.println(msg);
    }

    public static void statusil(String msgPart) {
        if (verbose)
            System.out.print(msgPart);
    }

    private static ChatCompletionRequest createCompletionRequest(List<ChatMessage> messages) {
        return ChatCompletionRequest
                .builder()
                .model("gpt-3.5-turbo")
                .messages(messages)
                .n(1)
                .maxTokens(2048)
                .logitBias(new HashMap<>())
                .build();
    }

    private static ChatMessage prepareInitialMessage(String classText, String pre, String post) {
        String msg = pre + "\n'''\n" + classText + "\n'''\n" + post;
        return userMessage(msg);
    }

    private static ChatMessage userMessage(String text) {
        return new ChatMessage(ChatMessageRole.USER.value(), text);
    }

    public static int lineOfMethod(List<String> lines, String methodName) {
        for(int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            Matcher m = method_decl.matcher(line);
            while (m.find() && m.group(2).equals(methodName)) {
                if (m.group(0).contains("class " + methodName))
                    continue;
                else return i;
            }
        }
        throw new RuntimeException("Location of method not found: " + methodName);
    }

    public static int lineOfFirstInvariantPlaceInMethod(List<String> lines, String methodName) {
        int ml = lineOfMethod(lines, methodName);
        // while for
        for (int i = ml; i < lines.size(); i++) {
            String l = lines.get(i);
            if (l.contains("for") || l.contains("while"))
                return i;
        }
        throw new RuntimeException("Location of loop statement not found: " + methodName);
    }

    public static String expandJMLBlock(List<String> lines, int expandFrom, int dir, String strt, String stop) {
//        Predicate<String> p = method_jml.asMatchPredicate();
//        if (!p.test(lines.get(expandFrom))) return null;
        boolean anyJML = false;
        boolean lineCmt = false;
        boolean blkCmt = false;
        if(lines.get(expandFrom).contains(strt))
            blkCmt = true;
        if(lines.get(expandFrom).contains("//"))
            lineCmt = true;
//        if (!lines.get(expandFrom).contains("@")) return null;
        if(!blkCmt || lineCmt) return null;
        int end = expandFrom;
        if (blkCmt) {
            String ln = lines.get(end);
            do {
                end += dir;
                ln = lines.get(end);
                anyJML |= ln.contains("@");
            } while (!ln.contains(stop));
        } else if (lineCmt) {
            anyJML |= lines.get(end).contains("@");
            while(lines.get(end+dir).contains("//")) {
                anyJML |= lines.get(end+dir).contains("@");
                end += dir;
            }
        } else return null;
        if (!anyJML) return null;
//        while (lines.get(end + dir).contains("@")) {
//            end += dir;
//        }
        int min = Math.min(expandFrom, end);
        int max = Math.max(expandFrom, end);
        int len = max - min + 1;
//        String jml = lines.stream().skip(min).limit(len).collect(Collectors.joining("\n"));
        // todo: select public normal_behavior or somtething like that
        List<String> relevant = lines.stream()
                .skip(min).limit(len)
                .filter(s -> !s.contains("@param") && !s.contains("@ param"))
                .collect(Collectors.toList());
        int atIndex = 0;
        for(String l : relevant) {
            int i =l.indexOf('@');
            if (i >= 0) {
                atIndex = i;
                break;
            }
        }
        final int ai = atIndex;
        Function<String, String> insertAts = s -> {
            int i = lines.indexOf('@');
             if (i == -1) {
                 return String.format("%"+(ai+1)+"s %s", "@", s);
             } else {
                 return String.format("%"+(ai+1)+"s", s.strip());
             }
        };

        for (int i = 0; i < relevant.size(); i++) {
            String s = relevant.get(i);
            String stripped = s.strip();
            if (stripped.startsWith("*") && !stripped.startsWith("*/")) {
                String better = s.replaceFirst("\\*", " ");
                relevant.set(i, better);
            }
        }

        if (true) {
            for (int i = 0; i < relevant.size(); i++) {
                String l = relevant.get(i);
                if (ai == l.indexOf("@")) continue;
                if (l.contains("/*")) {
                    String after = l.split("/\\*")[1];
                    String res = String.format("%" + (ai - 3) + "s %s", "/* @", after);
                    relevant.set(i, res);
                } else {
                    relevant.set(i, insertAts.apply(l.trim()));
                }
            }
        }

        String jml = relevant.stream().collect(Collectors.joining("\n"));
        return jml;
    }

    public static String extractCodeRegion(List<String> lines) {
        int begin, end;
        boolean found_begin = false;
        boolean finished = false;
        List<String> accum = new ArrayList<>();
        String ref = "/*@ public normal_behavior\n" +
                "  @ requires newSize >= 0;\n" +
                "  @ assignable size;\n" +
                "  @ ensures size == newSize;\n" +
                "*/";
        for(int i = 0; i < lines.size() && !finished; i++) {
            String l = lines.get(i);
            if (found_begin) {
                accum.add(l);
                if(l.contains("*/")) finished = true;
            } else {
                if (l.contains("/*")) {
                    found_begin = true;
                    accum.add(l);
                }
            }
        }
        return String.join("\n", accum);
//        Predicate<String> p = gpt_code_delim.asMatchPredicate();
//        while (!p.test(lines.get(i)) && i < lines.size()) i++;
//        int begin = i;
//        while (!p.test(lines.get(i)) && i < lines.size()) i++;
//        int end = i;
//        if (Math.abs(end - begin) <= 1) {
//            return null;
//        } else {
//            String region = lines.stream().skip(begin).limit(end - begin).collect(Collectors.joining("\n"));
//            return region;
//        }
    }

    public static class Pair<X, Y> {
        public final X x;
        public final Y y;
        public Pair(X x, Y y) {
            this.x = x;
            this.y = y;
        }
    }

    public static class Triple<X, Y, Z> {
        public final X x;
        public final Y y;
        public final Z z;
        public Triple(X x, Y y, Z z) {
            this.x = x;
            this.y = y;
            this.z = z;
        }
    }

    public enum FailureReason {
        NONE,
        NO_JML_IN_SEARCH_LOCATIONS,
        NO_JML_IN_REGION,
        INVALID_JAVA,
        WRONG_JML,
        UNKNOWN,
        UNKNOWN_FATAL
    }

    public static Pair<String, FailureReason> extractJML(String text, String methodName) {
        // Case 1: JML mixed with Java code:
        // Case 2: Pure JML
        List<String> lines = Arrays.asList(text.split("\\n"));
        try {
            int lineOfInterest = lineOfMethod(lines, methodName);
            String above = expandJMLBlock(lines, lineOfInterest - 1, -1, "*/", "/*");
            String below = expandJMLBlock(lines, lineOfInterest + 1, 1, "/*", "*/");
            if (above != null) return new Pair<>(above, FailureReason.NONE);
            else if (below != null) return new Pair<>(below, FailureReason.NONE);
            else return new Pair<>(null, FailureReason.NO_JML_IN_SEARCH_LOCATIONS);
        } catch (RuntimeException e) {
            if (e.getMessage().contains("Location of method not found:")) {
                String s = extractCodeRegion(lines);
                return new Pair<>(s, (s == null || s.isEmpty()) ? FailureReason.NO_JML_IN_REGION : FailureReason.NONE);
            } else throw e;
        }
    }

    public static Pair<String, FailureReason> extractInvariant(String text, String methodName) {
        // Case 1: JML mixed with Java code:
        // Case 2: Pure JML
        List<String> lines = Arrays.asList(text.split("\\n"));
        try {
            int lineOfInterest = lineOfFirstInvariantPlaceInMethod(lines, methodName);
            String above = expandJMLBlock(lines, lineOfInterest - 1, -1, "*/", "/*");
            String below = expandJMLBlock(lines, lineOfInterest + 1, 1, "/*", "*/");
            if (above != null) return new Pair<>(above, FailureReason.NONE);
            else if (below != null) return new Pair<>(below, FailureReason.NONE);
            else return new Pair<>(null, FailureReason.NO_JML_IN_SEARCH_LOCATIONS);
        } catch (RuntimeException e) {
            if (e.getMessage().contains("Location of method not found:")) {
                String s = extractCodeRegion(lines);
                return new Pair<>(s, (s == null || s.isEmpty()) ? FailureReason.NO_JML_IN_REGION : FailureReason.NONE);
            } else throw e;
        }
    }

    static class AutoClose<T> implements AutoCloseable {
        public final T val;
        private final Consumer<T> close;
        public AutoClose(T inner, Consumer<T> close) {
            this.val = inner;
            this.close = close;
        }

        @Override
        public void close() {
            System.err.println("Closing KeY Environment");
            if (close != null) { close.accept(val);}
            System.out.flush();
            System.err.flush();
        }
    }

    public static Triple<Boolean, FailureReason, Exception> tryKeyValidation(List<String> classLines, String methodName, String subfun, String jmlText, boolean isInvariant, Path tmpfile, FailureReason errSoFar) {
        if (errSoFar != FailureReason.NONE)
            return new Triple<>(false, errSoFar, null); // todo: this is hacky, but an easy way to short-circuit for now
        NodeList<com.github.javaparser.ast.Node> gptContracts;
        try {
            gptContracts = JmlHelper.parseFragment(jmlText);
        } catch (ParsingException e) {
            return new Triple<>(false, FailureReason.INVALID_JAVA, new Exception("Error during JML parsing: " + e.getMessage()));
        }
        CompilationUnit cu;
        try {
            cu = JmlHelper.parseFile(String.join("\n", classLines));
        } catch (ParsingException e) {
            throw new RuntimeException("Original Java File not parseable: " +e.getMessage());
        }

        if (isInvariant) {
            cu = JmlHelper.addLoopInvariant(cu, methodName, gptContracts);
        } else if (subfun != null) {
            cu = JmlHelper.addMethodContract(cu, subfun, gptContracts);
        } else {
            cu = JmlHelper.addMethodContract(cu, methodName, gptContracts);
        }
        String classToTest = cu.toString();
        try {
            Files.writeString(tmpfile, classToTest);
        } catch (IOException e) {
            status(e.toString());
            return new Triple<>(false, FailureReason.UNKNOWN_FATAL, null);
        }

        KeYEnvironment<?> env = null;
        // Path to the source code folder/file or to a *.proof file
        boolean foundRelevantContract = false;
        Triple<Boolean, FailureReason, Exception> preparedResult = null;
        try (AutoClose<KeYEnvironment<?>> envAuto = new AutoClose<>(Utility.createKeyEnvironment(tmpfile.toFile(), null, null, null), KeYEnvironment::dispose)) {
            // Ensure that Taclets are parsed
            //env = Utility.createKeyEnvironment(tmpfile.toFile(), null, null, null);
            env = envAuto.val;
            ImmutableList<ProgramVariable> projectionVariables = ImmutableList.fromList(new LinkedList<>());
            List<Contract> contracts = Utility.getContracts(env);
            status("Looking for contracts:");
            for (Contract c : contracts) {
                if (!(c instanceof FunctionalOperationContractImpl)) continue;
                FunctionalOperationContractImpl foc = (FunctionalOperationContractImpl) c; // todo: highly fragile
                ProgramMethod pm = (ProgramMethod) foc.pm;
                String pmName = pm.getName();
                System.out.println("* " + pmName);
                // TODO: Distinction failed top level vs. failed subcontract verification...
                if (pmName.contains(methodName)) { // Top Level Method: Always needs to be verified...
                    foundRelevantContract = true;
                    status("Found relevant contract: " + pmName);
                    var result = checkContract(env, c, projectionVariables);
                    if (result.y != FailureReason.NONE){
                        preparedResult = result;
                        break;
                    }
                }
                if (subfun!=null && pmName.contains(subfun)) { // If they exists, submethods should be verified...
                    foundRelevantContract = true;
                    status("Found relevant contract: " + pmName);
                    var result = checkContract(env, c, projectionVariables);
                    if (result.y != FailureReason.NONE){
                        preparedResult = result;
                        break;
                    }
                }
                if (Thread.interrupted()) {
                    status("Verification interrupted");
                    return new Triple<>(false, FailureReason.UNKNOWN, null);
                }
            }
        } catch (ProblemLoaderException e) {
            status("Encountered Exception: " + e.getClass().getName());
            status(e.toString());
//            status("please provide manual confirmation:");
//            Scanner scanner = new Scanner(System.in);
//            String userInput = scanner.nextLine();
//            if (userInput.equals("valid")) {
//                return new Pair<>(true, FailureReason.NONE);
//                // todo: here more sophisticated failure reasons AND prompts should be possible, as we already asked a person
//            }
            preparedResult = new Triple<>(false, FailureReason.INVALID_JAVA, e);
        }
        if (preparedResult != null) return preparedResult;
        if (!foundRelevantContract) return new Triple<>(false, FailureReason.UNKNOWN, null);
        status("All contracts verified or procedure was aborted.");
        return new Triple<>(true, FailureReason.NONE, null);
    }

    private static Triple<Boolean, FailureReason, Exception> checkContract(KeYEnvironment<?> env, Contract relevantContract, ImmutableList<ProgramVariable> projectionVariables) {
        List<UnclosedProof> unclosedProofs = Utility.tryClosingProofsAndListUnclosed(env, List.of(relevantContract), false, projectionVariables);
        if (unclosedProofs.isEmpty()) {
            status("No open proof found.");
            return new Triple<>(true, FailureReason.NONE, null);
        } else {

            // Some very simple idea to extract information about the open proof from KeY:
            var open = unclosedProofs.get(0);
            Proof p = open.proof;

            // For now, we just take the first open goal. Could be improved in the future (e.g.
            // scan through all open goals and prefer "Invariant Initially Valid" as feedback).
            status("FAILURE: Open proof found: ");
            List<String> openGoalsInfo = new LinkedList<>();
            for (Goal g: p.openGoals()) {
                String pathInfo = collectPathInformation(g.node());
                openGoalsInfo.add(pathInfo);
                status("Open Goal: " + pathInfo);
            }


            return new Triple<>(false, FailureReason.WRONG_JML, new VerificationException(openGoalsInfo));
        }
    }

    // Taken from class SourceView in KeY GUI
    /**
     * Collects the information from the tree to which branch the current node belongs:
     * <ul>
     * <li>Invariant Initially Valid</li>
     * <li>Body Preserves Invariant</li>
     * <li>Use Case</li>
     * <li>...</li>
     * </ul>
     *
     * @param node the current node
     * @return a String containing the path information to display
     */
    private static String collectPathInformation(Node node) {
        while (node != null) {
            if (node.getNodeInfo() != null && node.getNodeInfo().getBranchLabel() != null) {
                String label = node.getNodeInfo().getBranchLabel();
                /*
                 * Are there other interesting labels? Please feel free to add them here.
                 */
                if (label.equals("Invariant Initially Valid")
                    || label.equals("Invariant Preserved and Used") // for loop scope invariant
                    || label.equals("Body Preserves Invariant") || label.equals("Use Case")
                    || label.equals("Show Axiom Satisfiability") || label.startsWith("Pre (")
                    || label.startsWith("Exceptional Post (") // exceptional postcondition
                    || label.startsWith("Post (") // postcondition of a method
                    || label.contains("Normal Execution") || label.contains("Null Reference")
                    || label.contains("Index Out of Bounds") || label.contains("Validity")
                    || label.contains("Precondition") || label.contains("Usage")) {
                    return label;
                }
            }
            node = node.parent();
        }
        // if no label was found we have to prove the postcondition
        return "Show Postcondition/Assignable";
    }

    public static boolean specifyFunction(
            String token,
            List<String> classLines,
            String methodName,
            boolean isCtor,
            String subfun,
            boolean specInvariant,
            int maxTries,
            Path tmpFile) {
        OpenAiService service = new OpenAiService(token);
        List<ChatMessage> messages = new ArrayList<>();
        boolean keyCouldVerify = false;
        String methodToSearch = subfun != null ? subfun : methodName;

        messages.add(systemMessage);
        String task;
        {
            String mtyp = (isCtor ? "constructor " : "method ");
            if (subfun != null) {
                task =
                    "Please provide a JML annotation to the " + mtyp + "\"" + subfun +
                    "\" such that the contract specified by \"" + methodName + "\" is satisfied.";
            } else if (specInvariant){
                task =
                    "Please provide a loop invariant for the first loop construct of the " + mtyp + "\"" + methodName + "\".";
            } else {
                task =
                    "Please provide a JML annotation to the " + mtyp + "\""  +
                    methodName +
                    "\" such that its behaviour is correctly reflected as a method contract.";
            }
        }
        String classText = String.join("\n", classLines);
        ChatMessage initMsg = prepareInitialMessage(classText, task, "");
        messages.add(initMsg);
        status(STR_INIT_QUERY);
        status(initMsg.getContent());
        // for debug purposes
//        Scanner scanner = new Scanner(System.in);

        for (int currentTry = 0; currentTry < maxTries && !keyCouldVerify; currentTry++) {
            ChatCompletionRequest ccr = createCompletionRequest(messages);
            Flowable<ChatCompletionChunk> flowable = service.streamChatCompletion(ccr);

            AtomicBoolean isFirst = new AtomicBoolean(true);
            ChatMessage chatMessage = service
                    .mapStreamToAccumulator(flowable)
                    .doOnNext(acc -> {
                        if(isFirst.getAndSet(false)) {
                            status(STR_QUERY_RESPONSE);
                        }
                        if (acc.getMessageChunk().getContent() != null) {
                            statusil(acc.getMessageChunk().getContent());
                        }
                    })
                    .doOnComplete(() -> {status("");})
                    .lastElement()
                    .blockingGet()
                    .getAccumulatedMessage();
            messages.add(chatMessage);

            status(STR_PROCESSING);
            status("Extracting JML");
            var possible_jml_text = specInvariant ? extractInvariant(chatMessage.getContent(), methodToSearch) : extractJML(chatMessage.getContent(), methodToSearch);
            if (possible_jml_text.x != null) {
                status(possible_jml_text.x);
            }
            status ("Validating");
            FailureReason freason = FailureReason.NONE;
            String fjml ="";
            ProblemLoaderException fex = null;
            if (possible_jml_text.x == null) {
                freason = possible_jml_text.y;
            } else {
                fjml = possible_jml_text.x;
                Triple<Boolean, FailureReason, ProblemLoaderException> key_result;
                {
//                    key_result = tryKeyValidation(classLines, methodName, possible_jml_text.x, specInvariant, tmpFile, possible_jml_text.y);
                    ExecutorService executor = Executors.newSingleThreadExecutor();
                    int timeout = 100;
                    TimeUnit tou = TimeUnit.SECONDS;
                    Future<Triple<Boolean, FailureReason, ProblemLoaderException>> fut = executor.submit((Callable) () -> {
                        try {
                            return tryKeyValidation(classLines, methodName, subfun, possible_jml_text.x, specInvariant, tmpFile, possible_jml_text.y);
                        } catch (Exception e) {
                            System.out.println("KeY validation failed: " + e.toString());
                            e.printStackTrace();
                            return new Triple<>(false, FailureReason.UNKNOWN_FATAL, null);
                        }
                    });
                    try {
                        var kr = fut.get(timeout, tou);
                        key_result = new Triple<>(kr.x, kr.y, kr.z);
                    } catch (TimeoutException | InterruptedException | RuntimeException | ExecutionException e) {
                        System.out.println(e.toString());
                        e.printStackTrace();
                        key_result = new Triple<>(false, FailureReason.INVALID_JAVA, null);
                    } finally {
                        executor.shutdown();
                    }
                }
                if (key_result.x) {
                    status(STR_SUCCESS);
                    return true;
                } else if (key_result.y == FailureReason.UNKNOWN_FATAL) {
                    status("Encountered an irrecoverable problem");
                    status(STR_ABORT);
                    return false;
                }
                freason = key_result.y;
                fex = key_result.z;
            }

            if (currentTry < maxTries - 1) {
                status(STR_NEXT_QUERY);
                // prepare response query
                String resp = getResponse(freason, methodToSearch, fjml, fex, specInvariant);
                ChatMessage responseMsg = userMessage(resp);
                // print it
                status(resp);
                // add it to the message list
                messages.add(responseMsg);
            } else {
                status(STR_ABORT);
                return false;
            }
        }
        return false;
    }

    private static String getResponse(FailureReason reason, String methodName, String jml, ProblemLoaderException pex, boolean isInvariant) {
        String r = "";
        switch (reason) {
            case NONE:
                throw new RuntimeException("There is no useful response for a solved problem");
            case NO_JML_IN_SEARCH_LOCATIONS:
                return isInvariant ? "Please write the loop invariant directly above the first loop construct of '" + methodName + "'"
                        : "Please write the JML directly above the method declaration of '" + methodName + "'";
            case NO_JML_IN_REGION:
                return isInvariant ? "Please write the loop invariant directly above the first loop construct of '" + methodName + "'"
                        : "Please write some JML for the method '" + methodName + "' that solves the task into a code region";
            case INVALID_JAVA:
                return isInvariant ? "The provided code is not a valid loop-invariant"
                        : "The provided code is not valid JML";
            case WRONG_JML:
                if (isInvariant) {
                    r += "The provided JML loop invariant does not solve the task for '" + methodName + "'.\n;";
                    if (pex != null)
                        r += "This might describe the reason: \n" + pex.getMessage() + "\n";
                    r += "Please use this to fix the following: \n";
                    r += jml;
                    return r;
                } else {
                    r += "The provided JML does not solve the task for '" + methodName + "'.\n;";
                    if (pex != null)
                        r += "This might describe the reason: \n" + pex.getMessage() + "\n";
                    r += "Please use this to fix the following: \n";
                    r += jml;
                    return r;
                }
            case UNKNOWN:
                r = isInvariant ? "Could you rephrase your solution? Please provide a valid JML loop invariant."
                    : "Could you rephrase your solution? Please only provide the JML contract.";
                if (pex != null)
                    r += "\nThis might describe the reason why change is required: \n" + pex.getMessage() + "\n";
                return r;
            case UNKNOWN_FATAL:
                throw new RuntimeException("There is no useful response for a fatal error problem");
        }
        return "";
    }
}

class VerificationException extends Exception {
    private List<String> problem_paths;
    public VerificationException(List<String> problem_paths) {
        super();
        this.problem_paths = problem_paths;
    }

    @Override
    public String toString() {
        return "During verification, the following proof branches could not be closed:\n" + String.join("\n", problem_paths);
    }

    @Override
    public String getMessage() {
        return toString();
    }
}