package org.keyproject.key.api;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.macros.ProofMacroFacade;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.scripts.ProofScriptCommandFacade;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.KeYConstants;
import org.eclipse.lsp4j.jsonrpc.CompletableFutures;
import org.eclipse.lsp4j.jsonrpc.messages.Either;
import org.eclipse.lsp4j.jsonrpc.services.JsonRequest;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.keyproject.key.api.data.*;
import org.keyproject.key.api.data.KeyIdentifications.*;
import org.keyproject.key.api.internal.NodeText;
import org.keyproject.key.api.remoteapi.ExampleDesc;
import org.keyproject.key.api.remoteapi.KeyApi;
import org.keyproject.key.api.remoteapi.PrintOptions;
import org.keyproject.key.api.remoteclient.ClientApi;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

public final class KeyApiImpl implements KeyApi {
    private final KeyIdentifications data = new KeyIdentifications();

    private ClientApi clientApi;
    private final ProverTaskListener clientListener = new ProverTaskListener() {
        @Override
        public void taskStarted(TaskStartedInfo info) {
            clientApi.taskStarted(info);
        }

        @Override
        public void taskProgress(int position) {
            clientApi.taskProgress(position);
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            clientApi.taskFinished(info);
        }
    };
    private final AtomicInteger uniqueCounter = new AtomicInteger();

    public KeyApiImpl() {
    }

    @Override
    @JsonRequest
    public CompletableFuture<List<ExampleDesc>> examples() {
        return CompletableFutures.computeAsync((c) ->
                ExampleChooser.listExamples(ExampleChooser.lookForExamples())
                        .stream().map(ExampleDesc::from).toList());
    }

    @Override
    public CompletableFuture<Boolean> shutdown() {
        return CompletableFuture.completedFuture(true);
    }

    @Override
    public void exit() {
    }

    @Override
    public void setTrace(SetTraceParams params) {

    }

    @Override
    public CompletableFuture<String> getVersion() {
        return CompletableFuture.completedFuture(KeYConstants.VERSION);
    }

    @Override
    public CompletableFuture<List<ProofMacroDesc>> getAvailableMacros() {
        return CompletableFuture.completedFuture(
                ProofMacroFacade.instance().getMacros().stream()
                        .map(ProofMacroDesc::from).toList()
        );
    }

    @Override
    public CompletableFuture<List<ProofScriptCommandDesc>> getAvailableScriptCommands() {
        return CompletableFuture.completedFuture(
                ProofScriptCommandFacade.instance().getScriptCommands().stream().map(ProofScriptCommandDesc::from).toList());
    }

    @Override
    public CompletableFuture<MacroStatistic> script(ProofId proofId, String scriptLine, StreategyOptions options) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            var env = data.find(proofId.env());
            var pe = new ProofScriptEngine(scriptLine, Location.UNDEFINED);

            try {
                pe.execute((AbstractUserInterfaceControl) env.getProofControl(), proof);
                return null;
            } catch (IOException | InterruptedException | ScriptException e) {
                throw new RuntimeException(e);
            }
        });
    }

    @Override
    public CompletableFuture<MacroStatistic> macro(ProofId proofId, String macroId, StreategyOptions options) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            var env = data.find(proofId.env());
            var macro = Objects.requireNonNull(ProofMacroFacade.instance().getMacro(macroId));

            try {
                var info = macro.applyTo(env.getUi(), proof, proof.openGoals(), null, clientListener);
                return MacroStatistic.from(proofId, info);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        });

    }

    @Override
    public CompletableFuture<MacroStatistic> auto(ProofId proofId, StreategyOptions options) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            var env = data.find(proofId.env());
            try {
                env.getProofControl().startAndWaitForAutoMode(proof);
                //clientListener);
                return null;//MacroStatistic.from(proofId, info);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        });

    }

    @Override
    public CompletableFuture<Boolean> dispose(ProofId id) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(id);
            data.dispose(id);
            proof.dispose();
            return true;
        });
    }

    @Override
    public CompletableFuture<List<NodeDesc>> goals(ProofId proofId, boolean onlyOpened, boolean onlyEnabled) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            if (onlyOpened && !onlyEnabled) {
                return asNodeDesc(proofId, proof.openGoals());
            } else if (onlyEnabled && onlyOpened) {
                return asNodeDesc(proofId, proof.openEnabledGoals());
            } else {
                return asNodeDesc(proofId, proof.allGoals());
            }
        });
    }

    private List<NodeDesc> asNodeDesc(ProofId proofId, ImmutableList<Goal> goals) {
        return asNodeDesc(proofId, goals.stream().map(Goal::node));
    }

    private List<NodeDesc> asNodeDesc(ProofId proofId, Stream<Node> nodes) {
        return nodes.map(it -> asNodeDesc(proofId, it)).toList();
    }

    private NodeDesc asNodeDesc(ProofId proofId, Node it) {
        return new NodeDesc(proofId, it.serialNr(), it.getNodeInfo().getBranchLabel(),
                it.getNodeInfo().getScriptRuleApplication());
    }

    @Override
    public CompletableFuture<NodeDesc> tree(ProofId proofId) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            return asNodeDescRecursive(proofId, proof.root());
        });
    }

    private NodeDesc asNodeDescRecursive(ProofId proofId, Node root) {
        final List<NodeDesc> list = root.childrenStream().map(it -> asNodeDescRecursive(proofId, it)).toList();
        return new NodeDesc(new NodeId(proofId, root.serialNr()),
                root.getNodeInfo().getBranchLabel(),
                root.getNodeInfo().getScriptRuleApplication(),
                list
        );
    }

    @Override
    public CompletableFuture<NodeDesc> root(ProofId proofId) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            return asNodeDesc(proofId, proof.root());
        });
    }

    @Override
    public CompletableFuture<List<NodeDesc>> children(NodeId nodeId) {
        return CompletableFuture.supplyAsync(() -> {
            var node = data.find(nodeId);
            return asNodeDesc(nodeId.proofId(), node.childrenStream());
        });
    }

    @Override
    public CompletableFuture<List<NodeDesc>> pruneTo(NodeId nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<Statistics> statistics(ProofId proofId) {
        return CompletableFuture.supplyAsync(() -> {
            var proof = data.find(proofId);
            return proof.getStatistics();
        });
    }

    @Override
    public CompletableFuture<TreeNodeDesc> treeRoot(ProofId proof) {
        return null;
    }

    @Override
    public CompletableFuture<List<TreeNodeDesc>> treeChildren(ProofId proof, TreeNodeId nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<List<TreeNodeDesc>> treeSubtree(ProofId proof, TreeNodeId nodeId) {
        return null;
    }

    @Override
    public CompletableFuture<List<SortDesc>> sorts(EnvironmentId envId) {
        return CompletableFuture.supplyAsync(() -> {
            var env = data.find(envId);
            var sorts = env.getServices().getNamespaces().sorts().allElements();
            return sorts.stream().map(SortDesc::from).toList();
        });
    }

    @Override
    public CompletableFuture<List<FunctionDesc>> functions(EnvironmentId envId) {
        return CompletableFuture.supplyAsync(() -> {
            var env = data.find(envId);
            var functions = env.getServices().getNamespaces().functions().allElements();
            return functions.stream().map(FunctionDesc::from).toList();
        });
    }

    @Override
    public CompletableFuture<List<ContractDesc>> contracts(EnvironmentId envId) {
        return CompletableFuture.supplyAsync(() -> {
            var env = data.find(envId);
            var contracts = env.getAvailableContracts();
            return contracts.stream().map(it -> ContractDesc.from(envId, env.getServices(), it)).toList();
        });
    }

    @Override
    public CompletableFuture<ProofId> openContract(ContractId contractId) {
        return CompletableFuture.supplyAsync(() -> {
            var env = data.find(contractId.envId());
            var contracts = env.getAvailableContracts();
            var contract = contracts.stream().filter(it -> it.id() == contractId.contractId()).findFirst();
            if (contract.isPresent()) {
                try {
                    var proof = env.createProof(contract.get().createProofObl(env.getInitConfig()));
                    return data.register(contractId.envId(), proof);
                } catch (ProofInputException e) {
                    throw new RuntimeException(e);
                }
            } else {
                return null;
            }
        });
    }

    @Override
    public CompletableFuture<NodeTextDesc> print(NodeId nodeId, PrintOptions options) {
        return CompletableFuture.supplyAsync(() -> {
            var node = data.find(nodeId);
            var env = data.find(nodeId.proofId().env());
            var notInfo = new NotationInfo();
            final var layouter = new PosTableLayouter(options.width(), options.indentation(), options.pure());
            var lp = new LogicPrinter(notInfo, env.getServices(), layouter);
            lp.printSequent(node.sequent());

            var id = new NodeTextId(nodeId, uniqueCounter.getAndIncrement());
            var t = new NodeText(lp.result(), layouter.getInitialPositionTable());
            data.register(id, t);
            return new NodeTextDesc(id, lp.result());
        });
    }

    private final IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter();

    @Override
    public CompletableFuture<List<TermActionDesc>> actions(NodeTextId printId, int pos) {
        return CompletableFuture.supplyAsync(() -> {
            var node = data.find(printId.nodeId());
            var proof = data.find(printId.nodeId().proofId());
            var goal = proof.getOpenGoal(node);
            var nodeText = data.find(printId);
            var pis = nodeText.table().getPosInSequent(pos, filter);
            return new TermActionUtil(printId, data.find(printId.nodeId().proofId().env()), pis, goal)
                    .getActions();
        });

    }

    @Override
    public CompletableFuture<List<TermActionDesc>> applyAction(TermActionId id) {
        return null;
    }

    @Override
    public void freePrint(NodeTextId printId) {
        CompletableFuture.runAsync(() -> data.dispose(printId));
    }

    public void setClientApi(ClientApi remoteProxy) {
        clientApi = remoteProxy;
    }

    private final DefaultUserInterfaceControl control = new MyDefaultUserInterfaceControl();

    @Override
    public CompletableFuture<ProofId> loadExample(String id) {
        return CompletableFutures.computeAsync((c) -> {
            var examples = ExampleChooser.listExamples(ExampleChooser.lookForExamples())
                    .stream().filter(it -> it.getName().equals(id)).findFirst();
            if (examples.isPresent()) {
                var ex = examples.get();
                Proof proof = null;
                KeYEnvironment<?> env = null;
                try {
                    var loader = control.load(JavaProfile.getDefaultProfile(),
                            ex.getObligationFile(), null, null, null, null, true, null);
                    InitConfig initConfig = loader.getInitConfig();

                    env = new KeYEnvironment<>(control, initConfig, loader.getProof(),
                            loader.getProofScript(), loader.getResult());
                    var envId = new EnvironmentId(env.toString());
                    data.register(envId, env);
                    proof = Objects.requireNonNull(env.getLoadedProof());
                    var proofId = new ProofId(envId, proof.name().toString());
                    return data.register(proofId, proof);
                } catch (ProblemLoaderException e) {
                    if (proof != null) proof.dispose();
                    if (env != null) env.dispose();
                    throw new RuntimeException(e);
                }
            }
            throw new IllegalArgumentException("Unknown example");
        });
    }

    @Override
    public CompletableFuture<ProofId> loadProblem(ProblemDefinition problem) {
        return CompletableFutures.computeAsync((c) -> {
            Proof proof = null;
            KeYEnvironment<?> env = null;
              /*  var loader = control.load(JavaProfile.getDefaultProfile(),
                        ex.getObligationFile(), null, null, null, null, true, null);
                InitConfig initConfig = loader.getInitConfig();

                env = new KeYEnvironment<>(control, initConfig, loader.getProof(),
                        loader.getProofScript(), loader.getResult());
                var envId = new EnvironmentId(env.toString());
                data.register(envId, env);
                proof = Objects.requireNonNull(env.getLoadedProof());
                var proofId = new ProofId(envId, proof.name().toString());
                return data.register(proofId, proof);*/
            return null;
        });

    }

    @Override
    public CompletableFuture<ProofId> loadKey(String content) {
        return CompletableFutures.computeAsync((c) -> {
            Proof proof = null;
            KeYEnvironment<?> env = null;
            try {
                final var tempFile = File.createTempFile("json-rpc-", ".key");
                Files.writeString(tempFile.toPath(), content);
                var loader = control.load(JavaProfile.getDefaultProfile(),
                        tempFile, null, null, null, null, true, null);
                InitConfig initConfig = loader.getInitConfig();
                env = new KeYEnvironment<>(control, initConfig, loader.getProof(),
                        loader.getProofScript(), loader.getResult());
                var envId = new EnvironmentId(env.toString());
                data.register(envId, env);
                proof = Objects.requireNonNull(env.getLoadedProof());
                var proofId = new ProofId(envId, proof.name().toString());
                return data.register(proofId, proof);
            } catch (ProblemLoaderException | IOException e) {
                if (proof != null) proof.dispose();
                if (env != null) env.dispose();
                throw new RuntimeException(e);
            }
        });
    }

    @Override
    public CompletableFuture<ProofId> loadTerm(String term) {
        return loadKey("\\problem{ " + term + " }");
    }

    @Override
    public CompletableFuture<Either<EnvironmentId, ProofId>> load(LoadParams params) {
        return CompletableFutures.computeAsync((c) -> {
            Proof proof = null;
            KeYEnvironment<?> env = null;
            try {
                var loader = control.load(JavaProfile.getDefaultProfile(),
                        params.keyFile(),
                        params.classPath(),
                        params.bootClassPath(),
                        params.includes(),
                        null,
                        true,
                        null);
                InitConfig initConfig = loader.getInitConfig();
                env = new KeYEnvironment<>(control, initConfig, loader.getProof(),
                        loader.getProofScript(), loader.getResult());
                var envId = new EnvironmentId(env.toString());
                data.register(envId, env);
                if ((proof = env.getLoadedProof()) != null) {
                    var proofId = new ProofId(envId, proof.name().toString());
                    return Either.forRight(data.register(proofId, proof));
                } else {
                    return Either.forLeft(envId);
                }
            } catch (ProblemLoaderException e) {
                if (proof != null) proof.dispose();
                if (env != null) env.dispose();
                throw new RuntimeException(e);
            }
        });
    }

    private class MyDefaultUserInterfaceControl extends DefaultUserInterfaceControl {
        @Override
        public void taskStarted(TaskStartedInfo info) {
            clientApi.taskStarted(info);
        }

        @Override
        public void taskProgress(int position) {
            clientApi.taskProgress(position);
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            clientApi.taskFinished(info);
        }

        @Override
        protected void macroStarted(TaskStartedInfo info) {
            clientApi.taskStarted(info);
        }

        @Override
        protected synchronized void macroFinished(ProofMacroFinishedInfo info) {
            clientApi.taskFinished(info);
        }

        @Override
        public void loadingStarted(AbstractProblemLoader loader) {
            super.loadingStarted(loader);
        }

        @Override
        public void loadingFinished(AbstractProblemLoader loader, IPersistablePO.LoadedPOContainer poContainer, ProofAggregate proofList, AbstractProblemLoader.ReplayResult result) throws ProblemLoaderException {
            super.loadingFinished(loader, poContainer, proofList, result);
        }

        @Override
        public void progressStarted(Object sender) {
            super.progressStarted(sender);
        }

        @Override
        public void progressStopped(Object sender) {
            super.progressStopped(sender);
        }

        @Override
        public void reportStatus(Object sender, String status, int progress) {
            super.reportStatus(sender, status, progress);
        }

        @Override
        public void reportStatus(Object sender, String status) {
            super.reportStatus(sender, status);
        }

        @Override
        public void resetStatus(Object sender) {
            super.resetStatus(sender);
        }

        @Override
        public void reportException(Object sender, ProofOblInput input, Exception e) {
            super.reportException(sender, input, e);
        }

        @Override
        public void setProgress(int progress) {
            super.setProgress(progress);
        }

        @Override
        public void setMaximum(int maximum) {
            super.setMaximum(maximum);
        }

        @Override
        public void reportWarnings(ImmutableSet<PositionedString> warnings) {
            super.reportWarnings(warnings);
        }

        @Override
        public void showIssueDialog(Collection<PositionedString> issues) {
            super.showIssueDialog(issues);
        }
    }


}
