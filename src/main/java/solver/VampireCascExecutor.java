package solver;

import com.microsoft.z3.Solver;

import java.util.concurrent.CountDownLatch;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class VampireCascExecutor extends SMTExecutor {
    private static String[] command = new String[]{
            "term_to_kill",
            "vampire",
            "--input_syntax", "smtlib2",
            "--proof", "off",
            "--output_mode", "smtcomp",
            "--mode", "portfolio",
            "--schedule", "casc",
    };

    public VampireCascExecutor(String solver, CountDownLatch latch, boolean satConclusive, boolean unsatConclusive) {
        super(handleStrings(solver), latch, command, satConclusive, unsatConclusive);
    }

    private static String processStringsInFormula(String formula) {
        Pattern pattern = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"");
        Matcher matcher = pattern.matcher(formula);
        StringBuffer out = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(out, "");
            out.append(StringUtil.expandStringToInteger(matcher.group(1)));
        }
        matcher.appendTail(out);
        return out.toString();
    }

    private static String handleStrings(String smt) {
        return "(define-sort String () Int)" + processStringsInFormula(smt);
    }
}
