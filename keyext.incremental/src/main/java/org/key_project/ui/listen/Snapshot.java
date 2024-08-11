/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.listen;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.util.Pair;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class Snapshot {

    private static Pattern SCRIPT_PATTERN = Pattern.compile(
            "/\\*@\\s*assert\\s+([A-Za-z0-9_]+)\\s*:[^{}]+\\\\by\\s*\\{(.*?)\\}\\s*;\\s*@?\\*/",
            Pattern.DOTALL);

    private Proof proof;
    private final Map<String, String> fileMap = new HashMap<>();
    private final Map<String, String> scriptMap = new HashMap<>();

    public static Snapshot fromFile(String file) throws ProofInputException, IOException {
        KeYFile keYFile = new KeYFile(file, new File(file), null, new JavaProfile());
        String javaPath = keYFile.readJavaPath();
        List<File> javaFiles = new ArrayList<>();
        collectJavaFiles(new File(javaPath), javaFiles);
        Snapshot result = new Snapshot();
        for (File javaFile : javaFiles) {
            result.handleJavaFile(javaFile);
        }
        return result;
    }

    private void handleJavaFile(File javaFile) throws IOException {
        String content = Files.readString(javaFile.toPath());
        Matcher matcher = SCRIPT_PATTERN.matcher(content);
        LinkedList<Pair<Integer, Integer>> removals = new LinkedList<>();
        while(matcher.find()) {
            String scriptName = matcher.group(1);
            String scriptContent = matcher.group(2);
            if(scriptMap.containsKey(scriptName)) {
                throw new IOException("Script " + scriptName + " defined multiple times");
            }
            scriptMap.put(scriptName, scriptContent);
            removals.addFirst(new Pair<>(matcher.start(2), matcher.end(2)));
        }

        StringBuilder sb = new StringBuilder(content);
        for (Pair<Integer, Integer> removal : removals) {
            sb.replace(removal.first, removal.second, "<script>");
        }
        fileMap.put(javaFile.getName(), sb.toString());
    }

    private static void collectJavaFiles(File file, List<File> javaFiles) {
        if(file.getName().toLowerCase().endsWith(".java")) {
            javaFiles.add(file);
        } else if(file.isDirectory()) {
            for(File f : file.listFiles()) {
                collectJavaFiles(f, javaFiles);
            }
        }
    }

    public boolean equalsOutsideScripts(Snapshot snapshot) {
        return snapshot.fileMap.equals(fileMap);
    }

    public Proof getProof() {
        return proof;
    }

    public void setProof(Proof proof) {
        this.proof = proof;
    }

    public Set<String> getChangedScripts(Snapshot newSnapshot) {
        HashSet<String> result = new HashSet<>();
        for (String name : scriptMap.keySet()) {
            String script1 = scriptMap.get(name);
            String script2 = newSnapshot.scriptMap.get(name);
            if(!script2.equals(script1)) {
                result.add(name);
            }
        }
        return result;
    }

    public String getScript(String scriptName) {
        return scriptMap.get(scriptName);
    }
}
