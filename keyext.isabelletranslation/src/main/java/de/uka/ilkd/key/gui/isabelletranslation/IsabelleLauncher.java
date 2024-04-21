package de.uka.ilkd.key.gui.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.ListConverter;
import de.unruh.isabelle.mlvalue.MLFunction2;
import de.unruh.isabelle.mlvalue.MLFunction3;
import de.unruh.isabelle.mlvalue.MLValue;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Position;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.TheoryHeader;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

public class IsabelleLauncher {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    private final IsabelleTranslationSettings settings;
    private Isabelle isabelle;
    private Theory thy0;

    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) throws IOException {
        this.settings = settings;
    }

    public List<SledgehammerResult> try0ThenSledgehammerAll(List<IsabelleProblem> problems, long timeout_seconds) throws IOException {
        if (problems.isEmpty()) {
            return new ArrayList<>();
        }
        ArrayList<Path> sessionRoots = new ArrayList<>();
        sessionRoots.add(settings.getTranslationPath());
        try {
            Isabelle.Setup setup = JIsabelle.setupSetLogic("KeYTranslations",
                    JIsabelle.setupSetSessionRoots(sessionRoots,
                            JIsabelle.setupSetWorkingDirectory(settings.getTranslationPath(),
                                    JIsabelle.setup(settings.getIsabellePath()))));
            isabelle = new Isabelle(setup);
        } catch (Exception e) {
            LOGGER.error("Can't find Isabelle at {}", settings.getIsabellePath());
            throw new IOException("Can't find Isabelle at " + settings.getIsabellePath());
        }
        thy0 = beginTheory("theory Translation imports Main KeYTranslations.TranslationPreamble begin", settings.getTranslationPath(), isabelle);
        LOGGER.info("Setup complete, solver starting {} problems...", problems.size());
        List<SledgehammerResult> results = new ArrayList<>();
        for (IsabelleProblem problem : problems) {
            results.add(problem.try0ThenSledgehammer(isabelle, thy0, timeout_seconds));
        }
        LOGGER.info("Completed all problems");
        isabelle.destroy();
        return results;
    }

    private Theory beginTheory(String thyText, Path source, Isabelle isabelle) {
        MLFunction3<Path, TheoryHeader, scala.collection.immutable.List<Theory>, Theory> begin_theory =
                MLValue.compileFunction("fn (path, header, parents) => Resources.begin_theory path header parents", isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
        MLFunction2<String, Position, TheoryHeader> header_read = MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter(), Implicits.theoryHeaderConverter());

        TheoryHeader header = header_read.apply(thyText, Position.none(isabelle), isabelle, de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter())
                .retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
        Path topDir = source.getParent();
        return begin_theory.apply(topDir, header, header.imports(isabelle).map((String name) -> Theory.apply(name, isabelle)), isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()))
                .retrieveNow(Implicits.theoryConverter(), isabelle);
    }
}
