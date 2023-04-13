pragma circom 2.0.0;

// to check  0 <= in < 2^n
template Bits(n){
    signal input in;
    signal bits[n];
    var bitsum = 0;
    for (var i = 0; i < n; i++) {
        // in의 i번째 bit 
        bits[i] <-- (in >> i) & 1;          // in i개 shift 후 0x0001 과 비트마스킹
        bits[i] * (bits[i] - 1) === 0;      // bits[i] binary check
        bitsum = bitsum + 2 ** i * bits[i]; // bitsum에 누적
    }
    bitsum === in;  // if in >= 16, then in > bitsum
}

template Main(n) {
    signal input value;

    component bitsN = Bits(n);

    bitsN.in <== value;
}

component main = Main(64);
