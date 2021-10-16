import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicLong;

public class Mora5RoundAttack {

    /** Блокирующая очередь для передачи пар H, H' из оффлайн потока в онлайн потоки */
    private BlockingQueue<List<long[]>> pairsForOnline = new ArrayBlockingQueue(100);
    /** Счетчик проверенных пар */
    private AtomicLong checkedPairs = new AtomicLong(0);

    /** Переменная хранит истинное значение М для рассчета dR для разных пар H, H' */
    private long realM;

    /** Переменная используется для передачи найденного истинного значения М в метод attack главного потока для отображения*/
    private AtomicLong res = new AtomicLong(0);
    /** Переменная нужна для остановки онлайн потоков после нахождения истинного М */
    private boolean foundM = false;

    /**
     * Класс потока Оффлайн этапа. Поток перебирает комбинации dHW1 и dK3 и находит для них пары H, H'.
     * Затем складывает эти пары в очередь, откуда их для проверки берет поток Онлайн этапа.
     */
    public class Offline extends Thread {
        Mora m;

        public Offline (String name) {
            super(name);
            m = new Mora();
        }

        /**
         * Метод ищет решения для уравнения S(ΔHY2 ^ HY2) ^ S(HY2) = ΔHZ2.
         * Все возможные решения ищутся индивидуально для каждого из 16 полубайт и возвращаются
         * в виде двумерного списка.
         */
        private ArrayList<ArrayList<Integer>> findXParts(long dHY2, long dHZ2) {
            int dx, dy;
            ArrayList<ArrayList<Integer>> x_parts = new ArrayList<>();
            for (int i = 15; i >= 0; i--) {
                x_parts.add(new ArrayList<>());
                dx = (int) ((dHY2 >> (i * 4)) & 0xFL);
                dy = (int) ((dHZ2 >> (i * 4)) & 0xFL);
                for (int j = 1; j < 16; j++) {
                    if ((m.pi[j] ^ m.pi[j ^ dx]) == dy) {
                        x_parts.get(15 - i).add(j);
                    }
                }
                if (x_parts.get(15 - i).size() == 0)
                    return null;
            }
            return x_parts;
        }

        /**
         * Метод принимает на вход созданный методом findXParts() двумерный список и
         * составляет из его элементов все возможные комбинации, формируя таким образом
         * массив решений уравнения S(ΔHY2 ^ HY2) ^ S(HY2) = ΔHZ2.
         */
        private long[] buildSolutionsFromXParts(ArrayList<ArrayList<Integer>> xes) {
            int size = 1;
            for (ArrayList<Integer> arl : xes) {
                size *= arl.size();
            }
            long[] res = new long[size+2];
            int[] counters = new int[16];
            for (int i = 0; i < size; i++) {
                for (int j = 0; j < 16; j++) {
                    res[i] = (res[i] << 4) + ((xes.get(j).get(counters[j])) & 0xFL);
                }
                for (int j = 15; j >= 0; j--) {
                    if (counters[j] < xes.get(j).size() - 1) {
                        counters[j]++;
                        break;
                    } else {
                        counters[j] = 0;
                    }
                }
            }
            return res;
        }

        /**
         * Метод увеличивает на 1 полученное значение value, но только в активных полубайтвх с номерами hbytes_nums,
         * игнорируя неактивные полубайты.
         */
        private long nextStep(long value, int... hbytes_nums) {
            int index = hbytes_nums.length - 1;
            while (index >= 0 && ((value >>> ((15 - hbytes_nums[index]) * 4)) & 0xFL) == 15) {
                value ^= 14L << ((15 - hbytes_nums[index]) * 4);
                index--;
            }
            if (index != -1)
                value += 1L << ((15 - hbytes_nums[index]) * 4);
            return value;
        }

        /**
         * Метод проверяет соответствие разности полученных ключей K, K' желаемому паттерну. То есть проверяет, что
         * в разности Ki и Ki' все полубайты, не входящие в pattern, равны 0.
         */
        private boolean checkPattern(long K, long K_, Integer... pattern) {
            long dK = K ^ K_;
            ArrayList<Integer> ar_pattenr = new ArrayList<>(Arrays.asList(pattern));
            for (int i = 0; i < 16; i++) {
                if (!ar_pattenr.contains(i)) {
                    if ((dK >> ((15 - i) * 4) & 0xFL) != 0) {
                        return false;
                    }
                }
            }
            return true;
        }

        /**
         * Метод вычисляет все значения ключей из найденного HY2 и проверяет, совпадают ли их разности с ожидаемым
         * паттерном. Если совпадают, то пара добавляется в очередь для проверки потоком Онлайн этапа.
         * Иначе, пара отбрасывается. Чтобы уменьшить количество проверяемых Онлайн потоком пар, некоторые пары
         * случайным образом проопускаются благодаря тому, что инкремент равен не 1, а случайному значению
         * от 1 до 4000.
         */
        private void searchPairs(long[] solutions) {
            for (int i = 0; i < solutions.length-2; i += (int)(Math.random()*4000)) {
                long[] K = new long[7], K_ = new long[7];
                K[2] = solutions[i] ^ m.consts[1];
                K[1] = m.SReverse(m.P(m.LReverse(K[2]))) ^ m.consts[0];
                K[0] = m.SReverse(m.P(m.LReverse(K[1])));
                K[3] = m.L(m.P(m.S(solutions[i])));
                K[4] = m.L(m.P(m.S(K[3] ^ m.consts[2])));
                K[5] = m.L(m.P(m.S(K[4] ^ m.consts[3])));
                K[6] = m.L(m.P(m.S(K[5] ^ m.consts[4])));

                K_[3] = K[3] ^ solutions[solutions.length - 1];
                K_[2] = m.SReverse(m.P(m.LReverse(K_[3]))) ^ m.consts[1];
                K_[1] = m.SReverse(m.P(m.LReverse(K_[2]))) ^ m.consts[0];
                K_[0] = m.SReverse(m.P(m.LReverse(K_[1])));
                K_[4] = m.L(m.P(m.S(K_[3] ^ m.consts[2])));
                K_[5] = m.L(m.P(m.S(K_[4] ^ m.consts[3])));
                K_[6] = m.L(m.P(m.S(K_[5] ^ m.consts[4])));

                if (checkPattern(K[1], K_[1], 0, 1, 2, 3) &&
                        checkPattern(K[2], K_[2], 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) &&
                        checkPattern(K[3], K_[3], 0,1, 4,5, 8,9, 12,13) &&
                        checkPattern(K[4], K_[4], 0, 1, 2, 3, 4, 5, 6, 7)) {
                    try {
                        pairsForOnline.put(Arrays.asList(K, K_));
                    } catch (Exception e) {
                        System.out.println("Exception " + e);
                    }
                }
            }
        }

        /**
         * Метод перебирает все возможные комбинации DHW1 и DK3. Вычисляет из них
         * DHY2 и DHZ2 и ищет для них решения уравнения S(ΔHY2 ^ HY2) ^ S(HY2) = ΔHZ2. Если решения найдены, то
         * они передаются методу searchPairs() для поиска пар H, H'.
         */
        public void run() {
            long dHW1 = 0x1000100010001000L, dHY2;
            long dK3 =  0x1000100010001000L, dHZ2;
            ArrayList<ArrayList<Integer>> x_parts = new ArrayList<>();
            for (long z = 0; z < Math.pow(15,8); z++) {
                dHY2 = m.L(dHW1);
                dHZ2 = m.P(m.LReverse(dK3));
                x_parts = findXParts(dHY2, dHZ2);
                if (x_parts != null) {
                    long time = System.currentTimeMillis();
                    long[] solutions = buildSolutionsFromXParts(x_parts);
                    solutions[solutions.length-2] = dHW1;
                    solutions[solutions.length-1] = dK3;
                    searchPairs(solutions);
                }
                dK3 = nextStep(dK3, 0, 4, 8, 12);
                if (dK3 == 0x1000100010001000L) {
                    dHW1 = nextStep(dHW1, 0, 4, 8, 12);
                }
            }
        }

    }

    /**
     * Класс потока Онлайн этапа. Поток проверяет найденные Оффлайн потоком пары H, H'. Первым делом для каждой
     * пары вычисляется значение dR. Затем, для всех возможных 15^4 dY5 решается уравнение
     * S(ΔY5 ^ Y5) ^ S(Y5) = P^-1L^-1(ΔR ^ ΔK6 ^ ΔM). Каждое найденное решение проходит обратные преобразования
     * до Z1 и, если dZ1 = dHZ1, то до М. Затем М проверяется на истинность.
     */
    public class Online extends Thread {

        private long M;
        private long[] K = new long[0], K_ = new long[0];
        private Mora m;
        private long R, R_;

        public Online(String name) {
            super(name);
            m = new Mora();
            M = realM;
        }

        /**
         * Метод вычисляет R из H
         */
        private long getR() {
            long res = m.L(m.P(m.S(M ^ K[1])));
            res = m.L(m.P(m.S(res ^ K[2])));
            res = m.L(m.P(m.S(res ^ K[3])));
            res = m.L(m.P(m.S(res ^ K[4])));
            res = m.L(m.P(m.S(res ^ K[5])));
            res = res ^ K[6];
            return res;
        }

        /**
         * Метод вычисляет R' из H'
         */
        private long getR_() {
            long res = m.L(m.P(m.S(M ^ K_[1])));
            res = m.L(m.P(m.S(res ^ K_[2])));
            res = m.L(m.P(m.S(res ^ K_[3])));
            res = m.L(m.P(m.S(res ^ K_[4])));
            res = m.L(m.P(m.S(res ^ K_[5])));
            res = res ^ K_[6];
            return res;
        }

        /**
         * Метод увеличивает на 1 полученное значение value, но только в активных полубайтвх с номерами hbytes_nums,
         * игнорируя неактивные полубайты.
         */
        private long nextStep(long value, int... hbytes_nums) {
            int index = hbytes_nums.length - 1;
            while (index >= 0 && ((value >>> ((15 - hbytes_nums[index]) * 4)) & 0xFL) == 15) {
                value ^= 14L << ((15 - hbytes_nums[index]) * 4);
                index--;
            }
            if (index != -1)
                value += 1L << ((15 - hbytes_nums[index]) * 4);
            return value;
        }

        /**
         * Метод ищет решения для уравнения S(ΔY5 ^ Y5) ^ S(Y5) = P^-1L^-1(ΔR ^ ΔK6 ^ ΔM).
         * Все возможные решения ищутся индивидуально для каждого из 16 полубайт и возвращаются
         * в виде двумерного списка.
         */
        private ArrayList<ArrayList<Integer>> findXParts(long dY5, long val) {
            int dx, dy;
            ArrayList<ArrayList<Integer>> x_parts = new ArrayList<>();
            for (int i = 15; i >= 0; i--) {
                x_parts.add(new ArrayList<>());
                dx = (int) ((dY5 >> (i * 4)) & 0xFL);
                dy = (int) ((val >> (i * 4)) & 0xFL);
                for (int j = 0; j < 16; j++) {
                    if ((m.pi[j] ^ m.pi[j ^ dx]) == dy) {
                        x_parts.get(15 - i).add(j);
                    }
                }
                if (x_parts.get(15 - i).size() == 0)
                    return null;
            }
            return x_parts;
        }

        /**
         * Метод принимает на вход созданный методом findXParts() двумерный список и
         * составляет из его элементов все возможные комбинации, формируя таким образом
         * массив решений уравнения S(ΔY5 ^ Y5) ^ S(Y5) = P^-1L^-1(ΔR ^ ΔK6 ^ ΔM).
         */
        private long[] buildSolutionsFromXParts(ArrayList<ArrayList<Integer>> xes) {
            int size = 1;
            for (ArrayList<Integer> arl : xes) {
                size *= arl.size();
            }
            try {
                long[] res = new long[size+2];
                int[] counters = new int[16];
                for (int i = 0; i < size; i++) {
                    for (int j = 0; j < 16; j++) {
                        res[i] = (res[i] << 4) + ((xes.get(j).get(counters[j])) & 0xFL);
                    }
                    for (int j = 15; j >= 0; j--) {
                        if (counters[j] < xes.get(j).size() - 1) {
                            counters[j]++;
                            break;
                        } else {
                            counters[j] = 0;
                        }
                    }
                }
                return res;
            } catch (Exception e) {
                return null;
            }
        }

        /**
         * Метод проверяет найденное методом checkSolutions() значение М.
         * Критерии истинности М:
         * - M = M'
         * - Рассчитанный из M R = R из истинного М
         * - Рассчитанный из M' R' = R' из истинного М'
         * Если все условия удовлетворены, то М считается истинным.
         */
        public boolean checkM(long M, long M_) {
            long res = m.L(m.P(m.S(M ^ K[1])));
            long res_ = m.L(m.P(m.S(M_ ^ K_[1])));
            res = m.L(m.P(m.S(res ^ K[2])));
            res_ = m.L(m.P(m.S(res_ ^ K_[2])));
            res = m.L(m.P(m.S(res ^ K[3])));
            res_ = m.L(m.P(m.S(res_ ^ K_[3])));
            res = m.L(m.P(m.S(res ^ K[4])));
            res_ = m.L(m.P(m.S(res_ ^ K_[4])));
            res = m.L(m.P(m.S(res ^ K[5])));
            res_ = m.L(m.P(m.S(res_ ^ K_[5])));
            res = res ^ K[6];
            res_ = res_ ^ K_[6];
            return M == M_ && res == R && res_ == R_ ? true : false;
        }

        /**
         * Для всех найденных решений уравнения S(ΔY5 ^ Y5) ^ S(Y5) = P^-1L^-1(ΔR ^ ΔK6 ^ ΔM)
         * метод проводит обратные преобразования до Z1, Z1'. Если dZ1 = dHZ1, то вычисляются М, M'
         * и передаются методу checkM() для проверки на истинность. Иначе, решение отбрасывается.
         * Если М оказалось истинным, то оно записывается в переменную res, а также foundM устанавливается в true.
         * Это является сигналом остальным Онлайн потокам, что больше не нужно проверять решения, а также
         * главному потоку, что можно выводить найденное решение и завершать программу.
         */
        private void checkSolutions(long[] solutions, long dY5) {
            long Y4, Y4_, Y3, Y3_, Y2, Y2_, Z1, Z1_, M, M_;
            for (long solution: solutions) {
                if (foundM) break;
                Y4 = m.SReverse(m.P(m.LReverse(solution ^ K[5])));
                Y4_ = m.SReverse(m.P(m.LReverse(solution ^ dY5 ^ K_[5])));
                Y3 = m.SReverse(m.P(m.LReverse(Y4 ^ K[4])));
                Y3_ = m.SReverse(m.P(m.LReverse(Y4_ ^ K_[4])));
                Y2 = m.SReverse(m.P(m.LReverse(Y3 ^ K[3])));
                Y2_ = m.SReverse(m.P(m.LReverse(Y3_ ^ K_[3])));
                Z1 = m.P(m.LReverse(Y2 ^ K[2]));
                Z1_ = m.P(m.LReverse(Y2_ ^ K_[2]));
                if ((Z1 ^ Z1_) != (m.S(K[1] ^ m.consts[0]) ^ m.S(K_[1] ^ m.consts[0])))
                    continue;
                M_ = m.SReverse(Z1_) ^ K_[1];
                M = m.SReverse(Z1) ^ K[1];
                if (checkM(M, M_)) {
                    if (!foundM) {
                        foundM = true;
                        res.set(M);
                    }
                }
            }
        }

        /**
         * Метод берет найденные Оффлайн потоком пары H, H' из блокирующие очереди, вычисляя для них R, R'.
         * Затем перебираются все возможные значения dW4, из них вычисляются dY5 и для каждого из них
         * вычисляется уравнение S(ΔY5 ^ Y5) ^ S(Y5) = P^-1L^-1(ΔR ^ ΔK6 ^ ΔM). Если найдены решения, то
         * они передаются методу checkSolutions() для дальнейшей обработки.
         */
        public void run() {
            List<long[]> pairs;
            while (!foundM) {
                try {
                    pairs = pairsForOnline.take();
                    K = pairs.get(0);
                    K_ = pairs.get(1);
                } catch (Exception e) {
                    System.out.println("Exception " + e);
                }
                this.R = getR();
                this.R_ = getR_();
                long dR = this.R ^ this.R_;
                long dW4 = 0x1000100010002000L;
                ArrayList<ArrayList<Integer>> x_parts;
                while(dW4 != 0x1000100010001000L) {
                    x_parts = findXParts(m.L(dW4) ^ (K[5] ^ K_[5]), m.P(m.LReverse(dR ^ (K[6] ^ K_[6]))));
                    if (x_parts != null) {
                        long[] solutions = buildSolutionsFromXParts(x_parts);
                        checkSolutions(solutions, m.L(dW4) ^ (K[5] ^ K_[5]));
                    }
                    dW4 = nextStep(dW4, 0,4,8,12);
                }
                checkedPairs.incrementAndGet();
            }
        }

    }

    /**
     * Метод главного потока. Он запускает Оффлайн поток и Онлайн потоки в нужном количестве.
     * Раз в 15 секунд выводится информация о ходе работы программы. Когда истинное значение М найдено,
     * метод выводит его в консоль и завершает программу.
     */
    public void attack(int threadsNum, long realM) {
        this.realM = realM;
        Offline offline = new Offline("Offline 1");
        offline.start();
        for (int i = 0; i < threadsNum; i++) {
            new Online("Online " + i).start();
        }
        long startTime = System.currentTimeMillis();
        try {
            while (!foundM) {
                Thread.sleep(15000);
                System.out.println("\nОбновление данных:");
                System.out.println("Программа работает уже  : " + ((System.currentTimeMillis() - startTime) / 1000.0) + " секунд");
                System.out.println("Проверено пар H, H': " + checkedPairs.get());
                System.out.println("\n");
            }
            System.out.println("Было проверено " + checkedPairs.get() + " пар");
            System.out.println("Истинное значение М найдено за " + ((System.currentTimeMillis() - startTime) / 1000.0) + " секунд");
            System.out.println(Long.toHexString(res.get()));
            System.exit(0);
        } catch (Exception e) {

        }
    }

    /**
     * Статический метод для конфигурации атаки. Принимает на вход истинное значение М, которое будет взламываться,
     * а также желаемое количество Онлайн потоков, которые должны быть запущены.
     */
    public static void Attack (long realM, int threadsNum) {
        new Mora5RoundAttack().attack(threadsNum, realM);
    }

}
