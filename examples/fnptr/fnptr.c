int apply(int (*fn)(int), int x) {
    return fn(x);
}

int double_val(int x) {
    return x * 2;
}

int main() {
    return apply(double_val, 21) - 42;
}
