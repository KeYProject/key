import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.puppycrawl.tools.checkstyle.api.AuditEvent;
import com.puppycrawl.tools.checkstyle.api.AutomaticBean;
import com.puppycrawl.tools.checkstyle.api.Filter;

/**
 * This class implements a checkstyle filter which filters all messages
 * which correspond to lines which have been recently changed according
 * to a git-diff file provided to the filter.
 *
 * <h2>Diff file</h2>
 * The git-diff file must be provided and is not produced by the filter.
 * You may create it using
 *
 * <pre>git diff -U0 $MERGE_BASE &gt; diffFile</pre>
 *
 * For <code>MERGE_BASE</code> the assignment
 *
 * <pre>MERGE_BASE=`git merge-base HEAD origin/main`</pre>
 *
 * proved sensible if merging against the main branch.
 * The <code>diffFile</code> can then be provided to the filter as
 * <pre> &lt;module name="GitDiffFilter"&gt;
 *   &lt;property name="diffFilename" value="diffFile" /&gt;
 * &lt;/module&gt;</pre>
 *
 * @author Mattias Ulbrich
 * @version 1
 * @since Mar 2017
 */
public final class GitDiffFilter extends AutomaticBean implements Filter {

    private static class Interval {
        private final int from;
        private final int to;
        private Interval(int from, int to) {
            assert from > 0 && to >= from: from + "-" + to;
            this.from = from;
            this.to = to;
        }

        public int compareTo(int val) {
            if(val < from) {
                return -1;
            } else if(val > to) {
                return +1;
            } else {
                return 0;
            }
        }

        @Override
        public String toString() {
            return "[" + from + ", " + to + "]";
        }
    }

    private final Pattern FILENAME_PATTERN = Pattern.compile("\\+\\+\\+ b/(.*)");
    private final Pattern CHANGE_PATTERN = Pattern.compile("@@ -[^ ]+ \\+(\\d+)(?:,(\\d+))? @@.*");

    private String diffFilename = null;
    private String filenamePrefix = null;
    private Map<String, List<Interval>> changedLines = null;


    public void setDiffFilename(String filename) {
        this.diffFilename = filename;
    }

    public void setFilenamePrefix(String prefix) {
        this.filenamePrefix = prefix;
    }

    @Override
    public boolean accept(AuditEvent event) {
        if(changedLines == null) {
            computeChangedLines();
        }

        String filename;
	filename = event.getFileName();
        // try {
        //     filename = new File(event.getFileName()).getAbsoluteFile().getCanonicalPath();
        // } catch (IOException e) {
        //     throw new RuntimeException(e);
        // }
        List<Interval> intervals = changedLines.get(filename);

        if(intervals == null) {
            return false;
        }

        assert find(intervals, event.getLine()) == findSimple(intervals, event.getLine());

        return find(intervals, event.getLine());
    }

    private void computeChangedLines() {

        Map<String, List<Interval>> result = new HashMap<String, List<Interval>>();

        try(BufferedReader br = new BufferedReader(new FileReader(diffFilename))) {

            String filename = null;
            String line;
            while((line = br.readLine()) != null) {
                Matcher m = FILENAME_PATTERN.matcher(line);
                if(m.matches()) {
                    filename = m.group(1);
		    if(filenamePrefix != null)
			filename = filenamePrefix + File.separator + filename;
                    // filename = new File(filename).getAbsoluteFile().getCanonicalPath();
                    result.put(filename, new ArrayList<Interval>());
                    continue;
                }

                m = CHANGE_PATTERN.matcher(line);
                if(m.matches()) {
                    int from = Integer.parseInt(m.group(1));
                    String toString = m.group(2);
                    int len = toString != null ? Integer.parseInt(toString) : 1;

                    // store this interval only if it is not a deletion.
                    if(len > 0) {
                        if(filename == null) {
                            throw new RuntimeException();
                        }

                        List<Interval> list = result.get(filename);

                        list.add(new Interval(from, from+len-1));
                    }
                }
            }

        } catch(IOException ioex) {
            throw new RuntimeException(ioex);
        }

        this.changedLines = result;
    }

    private boolean find(List<Interval> intervals, int value) {
        int lo = 0;
        int hi = intervals.size() - 1;

        while(lo <= hi) {
            int mid = (lo+hi) >>> 1;
            Interval midInterval = intervals.get(mid);
            switch(midInterval.compareTo(value)) {
            case -1: hi = mid-1; break;
            case +1: lo = mid+1; break;
            case 0: return true;
            }
        }

        return false;
//        return intervals.get(lo).compareTo(value) == 0;
    }

    // A comparison implementation to ensure binsearch works correctly
    private boolean findSimple(List<Interval> intervals, int value) {
        for (Interval interval : intervals) {
            if(interval.compareTo(value) == 0) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void finishLocalSetup() {
    }
}
