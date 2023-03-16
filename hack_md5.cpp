#include <string>
#include <iostream>
#include <bitset>
#include <math.h>

// Array with right shifts data for all 4 rounds by 16 steps
const int S[64] = {
    7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
};

// Array with const 2^32 × abs (sin(i + 1))
const std::uint32_t K[64] = { 
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
    0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
    0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
    0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
    0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
    0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
    0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
    0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
    0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391 
};

inline std::uint32_t F(const std::uint32_t x, const std::uint32_t y, const std::uint32_t z)
{
    return x & y | ~x & z;
}

inline std::uint32_t G(const std::uint32_t x, const std::uint32_t y, const std::uint32_t z)
{
    return x & z | y & ~z;
}

inline std::uint32_t H(const std::uint32_t x, const std::uint32_t y, const std::uint32_t z)
{
    return x ^ y ^ z;
}

inline std::uint32_t I(const std::uint32_t x, const std::uint32_t y, const std::uint32_t z)
{
    return y ^ (x | ~z);
}

// Convert uint32 to string with hex form of this number
std::string Uint32ToHexForm(std::uint32_t a)
{
    std::string res;
    
    for (int i = 0; i < 4; i++)
    {
        int lowByte = a % 16;
        a /= 16;
        
        int highByte = a % 16;
        a /= 16;

        if (highByte > 9)
        {
            if (highByte == 10) res += "a";
            if (highByte == 11) res += "b";
            if (highByte == 12) res += "c";
            if (highByte == 13) res += "d";
            if (highByte == 14) res += "e";
            if (highByte == 15) res += "f";
        }
        else
            res += std::to_string(highByte);

        if (lowByte > 9)
        {
            if (lowByte == 10) res += "a";
            if (lowByte == 11) res += "b";
            if (lowByte == 12) res += "c";
            if (lowByte == 13) res += "d";
            if (lowByte == 14) res += "e";
            if (lowByte == 15) res += "f";
        }
        else
            res += std::to_string(lowByte);
    }

    return res;
}

// This function makes right padding to source string.
// Its make string length equal 512 bits(64 chars) * N(unsigned int)
inline void StringPadding_MD5(std::string& str)
{
    // String length in bytes
    std::uint64_t stringLength = str.length() * 8;

    // Add one 1 bit and seven 0 bits to data end. It's equals adding 10000000 or 128 symbol to string end
    str += (char)128;

    // Adding additional bits to make data length equal 512*N + 448, or in chars 64*N + 56
    // Adding eight 0 bits to data end. It's equals adding 00000000 or 0 symbol to string end
    while (str.length() % 64 != 56)
        str += '\0';
    
    // String with source string size
    std::string stringAddition;

    // Pushing symbols to string. Equals 256 based count system
    while (stringLength / 256 > 0)
    {
        stringAddition += (char)(stringLength % 256);
        stringLength /= 256;
    } 

    stringAddition += (char)(stringLength % 256);  
    
    // Adding string addition chars to source string in right order
    // At first we add 4 last bytes(chars). After that we add 4 first bytes(chars).
    // Also this function change bytes position to next function CalculateHastStep_MD5
    for (int i = (stringAddition.length() - 1); i != -1; i--)
        str += stringAddition[stringAddition.length() - 1 - i];

    for (int i = 0; i < 8 - stringAddition.length(); i++)
        str += '\0'; 
}

// Calculate hash to 512 bits(64 chars) and change initial numbers
void CalculateHashStep_MD5(std::string str, std::uint32_t& A0, std::uint32_t& B0, std::uint32_t& C0, std::uint32_t& D0)
{
    // Convert every 4 chars to 32 bit int and save it into little endian
    std::uint32_t M[16];
    for (int i = str.length() - 1; i > -1; i -= 4)
    {
        M[i/4] = 0;
        M[i/4] |= (unsigned char)str[i] << 24;
        M[i/4] |= (unsigned char)str[i - 1] << 16;
        M[i/4] |= (unsigned char)str[i - 2] << 8;
        M[i/4] |= (unsigned char)str[i - 3];
    }

    // Save init uints values
    std::uint32_t A = A0;
    std::uint32_t B = B0;
    std::uint32_t C = C0;
    std::uint32_t D = D0;

    for (int i = 0; i < 64; i++)
    {       
        // New value
        std::uint32_t newVal;
        int g;
        std::uint32_t (*func)(const std::uint32_t, const std::uint32_t, const std::uint32_t);

        // Calculate F(B, C, D) = (B and C) or (not B and D)
        if (i < 16)
        {
            func = F; 
            g = i;
        }

        // Calculate G(B, C, D) = (B and D) or (C and not D)
        if (i >= 16 && i < 32)
        {
            func = G;
            g = (5 * i + 1) % 16;
        }

        // H(B, C, D) = B xor C xor D
        if (i >= 32 && i < 48)
        {
            func = H;
            g = (3 * i + 5) % 16;
        }

        // I(B, C, D) = C xor (B or not D)
        if (i >= 48) 
        {
            func = I;
            g = (7 * i) % 16;
        }

        switch(i % 4)
        {
        case 0:
            newVal = func(B, C, D) + A + K[i] + M[g];
            A = B + ((newVal << S[i]) | (newVal >> (32 - S[i])));
            break;

        case 1:
            newVal = func(A, B, C) + D + K[i] + M[g];
            D = A + ((newVal << S[i]) | (newVal >> ((sizeof(std::uint32_t) * 8) - S[i])));
            break;

        case 2:
            newVal = func(D, A, B) + C + K[i] + M[g];
            C = D + ((newVal << S[i]) | (newVal >> ((sizeof(std::uint32_t) * 8) - S[i])));
            break;
        case 3:
            newVal = func(C, D, A) + B + K[i] + M[g];
            B = C + ((newVal << S[i]) | (newVal >> ((sizeof(std::uint32_t) * 8) - S[i])));
            break;
        }
    }

    // Update initial variables
    A0 += A;
    B0 += B;
    C0 += C;
    D0 += D; 
}

std::string CalculateHash_MD5(std::string str)
{
    // A – 01 23 45 67 in little endian order: 67452301
    std::uint32_t A0 = 0x67452301;
    // B - 89 AB CD EF in little endian order: EFCDAB89
    std::uint32_t B0 = 0xefcdab89;
    // C – FE DC BA 98 in little endian order: 98BADCFE
    std::uint32_t C0 = 0x98badcfe;
    // D – 76 54 32 10 in little endian order: 10325476
    std::uint32_t D0 = 0x10325476;

    // Padding source string
    StringPadding_MD5(str);
    // Split source string to 512 bits(64 chars) chunks and process all of them
    for (int i = 0; i < str.length(); i += 64)
        CalculateHashStep_MD5(str.substr(i, 64), A0, B0, C0, D0);
    
    // Return changed initial uints converted to string with hex form
    return Uint32ToHexForm(A0) + Uint32ToHexForm(B0) + Uint32ToHexForm(C0) + Uint32ToHexForm(D0);
}

std::string Uint64ToString(std::uint64_t t)
{
    std::string res;
    while (t / 256 != 0)
    {
        res += t % 256;
        t /= 256;
    }

    res += t % 256;
    return res;
}

int main()
{
    std::string input = "9cdfb439c7876e703e307864c9167a15";

    // i - amount of symbol combinations
    for (std::uint64_t i = 0; i < 1000000000000; i++)
    {
        std::string str = Uint64ToString(i);
        // for (auto it : str`)
        //     std::cout << (int)(unsigned char)it << std::endl;

        // std::cout << std::endl;
        if (CalculateHash_MD5(str) == input)
        {
            std::cout << "Your string: " << str << std::endl;
            return 1;
        }
    }
    std::cout << "Not found" << std::endl;
}