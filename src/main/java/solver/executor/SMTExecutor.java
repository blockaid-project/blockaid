package solver.executor;

import com.microsoft.z3.Status;

import java.io.*;
import java.util.Arrays;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;

public abstract class SMTExecutor extends Thread {
    private String smtString;
    private CountDownLatch latch;
    private String[] command;
    private boolean satConclusive;
    private boolean unsatConclusive;
    private boolean runCore;

    private Status result = null;
    private String[] core = null;
    private Process process = null;
    private AtomicBoolean shuttingDown = new AtomicBoolean(false);

    protected SMTExecutor(String smtString, CountDownLatch latch, String[] command) {
        this(smtString, latch, command, false, true, true);
    }
    protected SMTExecutor(String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive, String name) {
        this(smtString, latch, command, satConclusive, unsatConclusive, false);
        setName(name);
    }
    protected SMTExecutor(String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive) {
        this(smtString, latch, command, satConclusive, unsatConclusive, false);
    }
    private SMTExecutor(String smtString, CountDownLatch latch, String[] command, boolean satConclusive, boolean unsatConclusive, boolean runCore) {
        this.smtString = smtString;
        this.latch = latch;
        this.command = command;
        this.satConclusive = satConclusive;
        this.unsatConclusive = unsatConclusive;
        this.runCore = runCore;
    }

    public void run() {
        if (this.runCore) {
            this.runUnsatCore();
        } else {
            this.runNormal();
        }
    }

    private void runNormal() {
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
            result = getResult(output.toString());
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
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
            result = Status.UNKNOWN;
        }
        if ((this.result == Status.UNSATISFIABLE && unsatConclusive) || (this.result == Status.SATISFIABLE && satConclusive)) {
            this.latch.countDown();
        } else {
            result = Status.UNKNOWN;
        }
    }

    private void runUnsatCore() {
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
                result = Status.UNKNOWN;
                return;
            }

            String[] parts = output.toString().split("\n", 2);
            result = getResult(parts[0].trim());
            String[] coreParts = parts[1].replace("\n", " ").replace("(", "").replace(")", "").trim().split("\\s+");
            core = Arrays.stream(coreParts).map(String::trim).toArray(String[]::new);
        } catch (InterruptedException e) {
            result = Status.UNKNOWN;
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
            result = Status.UNKNOWN;
        }
        if (this.result == Status.UNSATISFIABLE) {
            this.latch.countDown();
        } else {
            result = Status.UNKNOWN;
        }
    }

    private synchronized void startProcess() throws Exception {
        if (!this.shuttingDown.get()) {
            ProcessBuilder pb = new ProcessBuilder(command);
            process = pb.start();
        }
    }

    public synchronized void signalShutdown() {
        shuttingDown.set(true);
        if (process != null) {
            process.destroy();
        }
        this.interrupt();
    }

    public Status getResult() {
        return result;
    }

    public String[] getUnsatCore() {
        return core;
    }

    protected Status getResult(String output) {
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
