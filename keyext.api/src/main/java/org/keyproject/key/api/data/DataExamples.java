/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.ExecutionException;

import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.scripts.RuleCommand;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import org.jspecify.annotations.Nullable;
import org.keyproject.key.api.KeyApiImpl;
import org.keyproject.key.api.data.KeyIdentifications.EnvironmentId;
import org.keyproject.key.api.data.KeyIdentifications.ProofId;
import org.keyproject.key.api.remoteapi.ServerManagement;
import org.keyproject.key.api.remoteclient.ShowDocumentParams;
import org.keyproject.key.api.remoteclient.ShowDocumentResult;

public class DataExamples {
    private final KeyApiImpl impl = new KeyApiImpl();
    // private final KeyIdentifications.ProofId proof;

    public DataExamples() throws ExecutionException, InterruptedException {
        // var name = impl.examples().get().getFirst().name();
        // proof = impl.loadExample(name).get();
    }

    private static @Nullable DataExamples instance;
    private static final Map<String, String> cache = new TreeMap<>();
    private static final Gson gson = new GsonBuilder().setPrettyPrinting().create();

    public static @Nullable String get(String typeFullName) {
        try {
            if (cache.containsKey(typeFullName)) {
                return cache.get(typeFullName);
            }

            if (instance == null) {
                instance = new DataExamples();
            }

            var clazz = Class.forName(typeFullName);
            for (var method : instance.getClass().getMethods()) {
                if (method.getReturnType().equals(clazz)) {
                    var object = method.invoke(instance);
                    return gson.toJson(object);
                }
            }

            return null;
        } catch (ClassNotFoundException | ExecutionException | InterruptedException
                | IllegalAccessException | InvocationTargetException e) {
            throw new RuntimeException(e);
        }
    }


    /*
     * public ExampleDesc getExample() {
     * return ExampleChooser.listExamples(ExampleChooser.lookForExamples())
     * .stream().map(ExampleDesc::from).findFirst().orElseThrow();
     * }
     */

    public ServerManagement.SetTraceParams getTraceParams() {
        return new ServerManagement.SetTraceParams(TraceValue.Info);
    }

    public ProofStatus getProofStatus() {
        return new ProofStatus(getProofId(), 10, 23);
    }

    public LoadParams getLoadParams() {
        return new LoadParams(Uri.from(new File("/home/weigl/test.key")),
                List.of(), null, List.of());
    }


    public ProofId getProofId() {
        return new ProofId(getEnvId(), "proof-5");
    }

    public EnvironmentId getEnvId() {
        return new EnvironmentId("env-1");
    }

    public ShowDocumentParams getSDP() {
        return new ShowDocumentParams("", true, true, getTextRange());
    }

    public @Nullable TextRange getTextRange() {
        return new TextRange(25, 100);
    }

    public ShowDocumentResult getSDR() {
        return new ShowDocumentResult(true);
    }

    public TermActionDesc getTermActionDesc() {
        return new TermActionDesc(getTermActionId(), "andLeft", "Apply taclet 'andLeft'.",
            "rules", TermActionKind.Taclet);
    }

    private KeyIdentifications.TermActionId getTermActionId() {
        return new KeyIdentifications.TermActionId(getNodeId(), "0.1.0", "taclet-andLeft-010");
    }

    private KeyIdentifications.NodeId getNodeId() {
        return new KeyIdentifications.NodeId(getProofId(), "01010102");
    }

    public MacroDescription getMacroDescription() {
        return MacroDescription.from(new FinishSymbolicExecutionMacro());
    }

    public PrintOptions getPrintingOptions() {
        return new PrintOptions(true, 80, 4, true, false);
    }

    public ProofScriptCommandDesc getPSCDesc() throws ExecutionException, InterruptedException {
        return ProofScriptCommandDesc.from(new RuleCommand());
    }

    /*
     * public NodeTextDesc getNodeText() throws ExecutionException, InterruptedException {
     * var root = impl.treeRoot(proof).get();
     * return impl.print(root.id(), getPrintingOptions()).get();
     * }
     *
     * public FunctionDesc getFunctionDescription() throws ExecutionException, InterruptedException
     * {
     * return impl.functions(proof.env()).get().getFirst();
     * }
     *
     * public ProofScriptCommandDesc getPSCDesc() throws ExecutionException, InterruptedException {
     * return impl.getAvailableScriptCommands().get().getFirst();
     * }
     *
     * public SortDesc getSortDesc() throws ExecutionException, InterruptedException {
     * return impl.sorts(proof.env()).get().getFirst();
     * }
     */
}
