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

    protected ProcessSMTExecutor(String name, String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive, boolean unknownConclusive, boolean runCore) {
        super(name, latch, satConclusive, unsatConclusive, unknownConclusive, runCore);
        this.smtString = smtString;
        this.command = command;
    }

    @Override
    protected Status doRunNormal() throws InterruptedException {
        InputStream stderr = null;
        try {
            String smtString = this.smtString + "(check-sat)";

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
                output.append(s);
            }

            scanner = new Scanner(stderr);
            while (scanner.hasNextLine()) {
                System.err.println(scanner.nextLine());
            }

            process.waitFor();
            return getResult(output.toString());
        } catch (InterruptedException e) {
            return Status.UNKNOWN;
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
            return Status.UNKNOWN;
        }
    }

    @Override
    protected Status doRunUnsatCore() throws InterruptedException {
        InputStream stderr = null;
        try {
            String smtString = "(set-option :produce-unsat-cores true)" + this.smtString + "(check-sat)(get-unsat-core)";

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
                output.append(s).append('\n');
            }

            scanner = new Scanner(stderr);
            while (scanner.hasNextLine()) {
                System.err.println(scanner.nextLine());
            }

            process.waitFor();

            if (output.toString().trim().isEmpty()) {
                return Status.UNKNOWN;
            }

            String[] parts = output.toString().split("\n", 2);
            Status result = getResult(parts[0].trim());
            String[] coreParts = parts[1].replace("\n", " ").replace("(", "").replace(")", "").trim().split("\\s+");
            setUnsatCore(Arrays.stream(coreParts).map(String::trim).toArray(String[]::new));
            return result;
        } catch (InterruptedException e) {
            return Status.UNKNOWN;
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
            return Status.UNKNOWN;
        }
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

    private Status getResult(String output) {
        switch (output.trim()) {
            case "sat":
                return Status.SATISFIABLE;
            case "unsat":
                return Status.UNSATISFIABLE;
            default:
                return Status.UNKNOWN;
        }
    }
}
