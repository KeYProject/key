package org.key_project.key.llm;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import org.jspecify.annotations.Nullable;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmUtils {
    private static @Nullable LlmSession globalSession;

    public static LlmSession getSession(Proof proof) {
        return getSession(LlmSettings.INSTANCE, proof);
    }

    public static LlmSession getSession(LlmSettings settings, Proof proof) {
        if (proof != null) {
            var session = proof.lookup(LlmSession.class);
            if (session != null) {
                return session;
            }
            session = new LlmSession(settings.getApiEndpoint(), settings.getAuthToken());
            proof.register(session, LlmSession.class);
            return session;
        } else {
            if (globalSession == null) {
                globalSession = new LlmSession(settings.getApiEndpoint(), settings.getAuthToken());
            }
            return globalSession;
        }
    }

    public static LlmSession getSession() {
        return getSession(MainWindow.getInstance().getMediator().getSelectedProof());
    }

    public static List<URI> getPossibleFiles() throws IOException {
        return getPossibleFiles(MainWindow.getInstance().getMediator().getSelectedProof());
    }

    public static List<URI> getPossibleFiles(@Nullable Proof selectedProof) throws IOException {
        if (selectedProof == null) {
            return List.of();
        }

        // selectedProof.getEnv().getServicesForEnvironment().getJavaModel().getBootClassPath();
        // selectedProof.getEnv().getServicesForEnvironment().getJavaModel().getClassPath();
        final var javaModel = selectedProof.getEnv().getServicesForEnvironment().getJavaModel();
        if (javaModel == null) {
            return List.of();
        }

        var javaSrc = javaModel.getModelDir();

        if (Files.isRegularFile(javaSrc)) {
            return List.of(javaSrc.toUri());
        }

        try (var walker = Files.walk(javaSrc)) {
            return walker.filter(Files::isRegularFile).map(Path::toUri).toList();
        }
    }
}
