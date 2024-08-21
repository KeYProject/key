package key.isabelletranslation;

import de.uka.ilkd.key.proof.Goal;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.*;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.Option;
import scala.Tuple2;
import scala.collection.immutable.List;
import scala.collection.mutable.Builder;
import scala.concurrent.Await;
import scala.concurrent.Future;
import scala.concurrent.duration.Duration;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class IsabelleProblem {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProblem.class);
    private final Goal goal;
    private SledgehammerResult result = null;
    private final String preamble;
    private final String sequentTranslation;
    private final Collection<IsabelleSolverListener> listeners = new HashSet<>();

    public IsabelleProblem(Goal goal, String preamble, String sequentTranslation) {
        this.goal = goal;
        this.preamble = preamble;
        this.sequentTranslation = sequentTranslation;
    }

    public void addListener(IsabelleSolverListener listener) {
        listeners.add(listener);
    }

    public Goal getGoal() {
        return goal;
    }

    public String getSequentTranslation() {
        return sequentTranslation;
    }

    public String getPreamble() {
        return preamble;
    }

    public SledgehammerResult getResult() {
        return result;
    }

    protected void setResult(SledgehammerResult result) {
        this.result = result;
    }
}
