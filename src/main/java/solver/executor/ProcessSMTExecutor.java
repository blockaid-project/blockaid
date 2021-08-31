package solver.executor;

import com.microsoft.z3.Status;

import java.io.*;
import java.util.Arrays;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;

public abstract class ProcessSMTExecutor extends SMTExecutor {
    private final String smtString;
    private final String[] command;
    private Process process = null;
    private final AtomicBoolean shuttingDown = new AtomicBoolean(false);
    protected String output = null;

    protected ProcessSMTExecutor(String name, String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, latch, satConclusive, unsatConclusive, unknownConclusive, runCore);
        this.smtString = smtString;
        this.command = command;
    }

    // Sets this.output.
    public String doRunRaw() {
        InputStream stderr = null;
        try {
            startProcess();
            InputStream stdout = process.getInputStream();
            OutputStream stdin = process.getOutputStream();
            stderr = process.getErrorStream();

            BufferedWriter bufferedStdin = new BufferedWriter(new OutputStreamWriter(stdin));
            bufferedStdin.write(smtString);
            bufferedStdin.flush();
            bufferedStdin.close();

            Scanner scanner = new Scanner(stdout);
            StringBuilder output = new StringBuilder();
            while (scanner.hasNextLine()) {
                String s = scanner.nextLine();
                output.append(s).append("\n");
            }

            scanner = new Scanner(stderr);
            while (scanner.hasNextLine()) {
                System.err.println(scanner.nextLine());
            }

            process.waitFor();
            this.output = output.toString();
            return this.output;
        } catch (InterruptedException e) {
            this.output = null;
            return null;
        } catch (Exception e) {
            if (!(e instanceof IOException)) {
                // IO errors are expected when the process is killed before/while stdin is written because another
                // executor finished already.
                e.printStackTrace();
            }
            if (stderr != null) {
                Scanner scanner = new Scanner(stderr);
                while (scanner.hasNextLine()) {
                    System.err.println(scanner.nextLine());
                }
            }
            this.output = null;
            return null;
        }
    }

    @Override
    protected Status doRunNormal() {
        String output = doRunRaw();
        if (output == null) {
            return Status.UNKNOWN;
        }
        return getResult(output);
    }

    @Override
    protected Status doRunUnsatCore() {
        String output = doRunRaw();
        if (output == null || output.trim().isEmpty()) {
            return Status.UNKNOWN;
        }
        String[] parts = output.split("\n", 2);
        Status result = getResult(parts[0].trim());
        if (result == Status.UNSATISFIABLE) {
            String[] coreParts = parts[1].replace("\n", " ").replace("(", "").replace(")", "").trim().split("\\s+");
            setUnsatCore(Arrays.stream(coreParts).map(String::trim).toArray(String[]::new));
        }
        // If the formula was not determined to be unsat, no reason to set the unsat core.
        return result;
    }

    private synchronized void startProcess() throws Exception {
        if (!this.shuttingDown.get()) {
            ProcessBuilder pb = new ProcessBuilder(command);
            process = pb.start();
        }
    }

    @Override
    public synchronized void signalShutdown() {
        shuttingDown.set(true);
        if (process != null) {
            process.destroy();
        }
        this.interrupt();
    }

    public String getOutput() {
        return output;
    }

    private Status getResult(String output) {
        switch (output.split("\n", 2)[0].trim()) {
            case "sat":
                return Status.SATISFIABLE;
            case "unsat":
                return Status.UNSATISFIABLE;
            default:
                return Status.UNKNOWN;
        }
    }
}
