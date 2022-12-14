class testgt {

    void deadLoop() {
        int x = 5;
        int y = 5;
        int z = 100;
        while (x > y) {
            use(z);
        }
        dead(); // unreachable branch
    }

    void dead() {
    }

    void use(int n) {
    }
}
