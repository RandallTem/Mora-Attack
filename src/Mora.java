public class Mora {

    /** Таблица подстановок для S преобразования */
    public int[] pi = {15, 9, 1, 7, 13, 12, 2, 8, 6, 5, 14, 3, 0, 11, 4, 10};

    /** Обратная таблица подстановок для обратного S преобразования */
    private int[] pi_reverse = {12, 2, 6, 11, 14, 9, 8, 3, 7, 1, 15, 13, 5, 4, 10, 0};

    /** Таблица перестановок для P преобразования */
    private int[] tau = {0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15};

    /** Бинарная матрица размером 16х16 для прямого L преобразования */
    private int[] lp = {0x3a22, 0x483b, 0x59e5, 0xac52, 0x8511, 0x248c, 0xbd7b, 0x56b1,
            0x4b99, 0x1246, 0xcfac, 0xb3c9, 0x2cdd, 0x9123, 0x6e56, 0xc86d};

    /** Обратная бинарная матрица размером 16х16 для обратного L преобразования */
    private int[] lp_reverse = {0xF50D, 0xDF5D, 0xDDF8, 0x8DD7, 0xC17A, 0xAC1D, 0xDACC, 0xCDA0,
            0x9C75, 0x59C2, 0x259E, 0xE257, 0x090E, 0xE09E, 0xEE07, 0x7EE7};

    /** Константы, используемые в функции формирования временного ключа */
    public long[] consts = {0xc0164633575a9699L, 0x925b4ef49a5e7174L, 0x86a89cdcf673be26L,
            0x1885558f0eaca3f1L, 0xdcfc5b89e35e8439L, 0x54b9edc789464d23L,
            0xf80d49afde044bf9L, 0x8cbbdf71ccaa43f1L, 0xcb43af722cb520b9L};

    public long[] keys = new long[10];

    /**
     * Прямое S преобразование. Функция подстановки. Каждый полубайт из 64-битной входной последовательности заменяется
     * соответствующим полубайтом из таблицы подстановок pi
     */
    public long S(long k) {
        long new_k = 0;
        int index = 0;
        for (int j = 15; j >= 0; j--){
            index = (int)((k>>(4*j))&0xFL);
            new_k = (new_k << 4) + pi[index];
        }
        return new_k;
    }

    /**
     *  Обратное S преобразование. Функция подстановки. Каждый полубайт из 64-битной входной последовательности
     *  заменяется соответствующим полубайтом из обратной таблицы подстановок pi
     */
    public long SReverse(long k) {
        long new_k = 0;
        int index = 0;
        for (int j = 15; j >= 0; j--){
            index = (int)((k>>(4*j))&0xFL);
            new_k = (new_k << 4) + pi_reverse[index];
        }
        return new_k;
    }

    /**
     * P преобразование. Функция перестановки. Для каждой пары полубайт из входной последовательности происходит
     * замена одного полубайта другим.
     */
    public long P(long k) {
        long new_k = 0;
        int temp = 0;
        for (int i = 15; i >= 0; i--) {
            new_k = (new_k << 4) + ((k >> (4 * tau[i])) & 0xFL);
        }
        return new_k;
    }

    /**
     * Прямое линейное преобразование L. Представляет собой умножение 64-битного входного вектора на
     * бинарную матрицу A размерами 16x16.
     */
    public long L(long k) {
        long new_k = 0;
        for (int i = 3; i >= 0; i--) {
            short block = 0;
            for (int j = 15; j >= 0; j--) {
                if ((((k >> (i * 16)) >> j) & 1L) == 1)
                    block = (short)(block ^ lp[15-j]);
            }
            new_k = (new_k << 16) + (block & 0xFFFF);
        }
        return new_k;
    }

    /**
     * Обратное линейное преобразование L. Представляет собой умножение 64-битного входного вектора на
     * бинарную матрицу, обратную бинарной матрице для прямого L преобразования.
     */
    public long LReverse(long k) {
        long new_k = 0;
        for (int i = 3; i >= 0; i--) {
            short block = 0;
            for (int j = 15; j >= 0; j--) {
                if ((((k >> (i * 16)) >> j) & 1L) == 1)
                    block = (short)(block ^ lp_reverse[15-j]);
            }
            new_k = (new_k << 16) + (block & 0xFFFF);
        }
        return new_k;
    }

    /**
     * Функция отвечает за формирование временного ключа К на каждом раунде функции E(K, m)
     */
    public long KeySchedule(long k, int i) { //HXi = Ki
        long new_k = k ^ consts[i];          //HYi = Ki-1 xor Ci
        new_k = S(new_k);                    //HZi = S(HYi)
        new_k = P(new_k);                    //HWi = P(HZi)
        new_k = L(new_k);                    //Ki+1 = L(HWi)

        return new_k;
    }

    /**
     * Алгоритм блочного шифрования (XSPL-шифр) с размером блока равным размеру хэш-кода - 64 бита
     * */
    public long E(long k, long m) {           //X1 = M
        k = S(k);
        k = P(k);
        k = L(k);                             //K1 = LPS(H+N)
        keys[0] = k;
        long state = k ^ m;                   //Y1 = X1 xor K1
        for (int i = 0; i < 9; i++) {
            state = S(state);                 //Zi = S(Yi)
            state = P(state);                 //Wi = P(Zi)
            state = L(state);                 //Xi+1 = L(Wi)
            k = KeySchedule(k, i);            //Get Ki+1
            keys[i+1] = k;
            state = state ^ k;                //Yi+1 = Xi+1 xor Ki+1
        }
        long[] keys_new = new long[10];
        keys_new[0] = keys[0];
        for (int i = 1; i < 10; i++) {
            keys_new[i] = keys[i] ^ keys[0];
        }
        keys_new = new long[10];
        keys_new[0] = keys[0];
        for (int i = 1; i < 10; i++) {
            keys_new[i] = keys[i] ^ keys[i-1];
        }
        return state;
    }

    /**
     * Функция сжатия на основе конструкции Миягучи – Пренеля
     */
    public long G(long n, long m, long h) {
        return E(h ^ n, m) ^ h ^ m;
    }

    /**
     * Рассчет хэша для сообщения message
     */
    public long getHash(long[] message) {
        long h = 0, n = 0, sigma = 0;
        for (int i = 0; i < message.length; i++) {
            h = G(n, message[i], h);
            n = n + 64;
            sigma = sigma + message[i];
        }
        h = G(0, n, h);
        h = G(0, sigma, h);
        return h;
    }
}
