#include <string>
#include <vector>
#include <fstream>
#include <cstdint>
#include <iostream>

// Define the block size for working with files
// Must be multiple 64
#define CHUNK_SIZE 4096

/// \brief Array with right shifts data for all 4 rounds by 16 steps
const int S[64] = {
    7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
};

/// \brief Array with const 2^32 × abs (sin(i + 1))
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

/**
    \brief One of the internal functions of the Md5 hashing algorithm

    \param [in] x One number out of the total sum of the Md5 algorithm
    \param [in] y One number out of the total sum of the Md5 algorithm
    \param [in] z One number out of the total sum of the Md5 algorithm

    \return New number of the total sum of the Md5 algorithm
*/
inline std::uint32_t F(const std::uint32_t& x, const std::uint32_t& y, const std::uint32_t& z) noexcept
{
    return (x & y) | (~x & z);
}

/**
    \brief One of the internal functions of the Md5 hashing algorithm

    \param [in] x One number out of the total sum of the Md5 algorithm
    \param [in] y One number out of the total sum of the Md5 algorithm
    \param [in] z One number out of the total sum of the Md5 algorithm

    \return New number of the total sum of the Md5 algorithm
*/
inline std::uint32_t G(const std::uint32_t& x, const std::uint32_t& y, const std::uint32_t& z) noexcept
{
    return (x & z) | (y & ~z);
}

/**
    \brief One of the internal functions of the Md5 hashing algorithm

    \param [in] x One number out of the total sum of the Md5 algorithm
    \param [in] y One number out of the total sum of the Md5 algorithm
    \param [in] z One number out of the total sum of the Md5 algorithm

    \return New number of the total sum of the Md5 algorithm
*/
inline std::uint32_t H(const std::uint32_t& x, const std::uint32_t& y, const std::uint32_t& z) noexcept
{
    return x ^ y ^ z;
}

/**
    \brief One of the internal functions of the Md5 hashing algorithm

    \param [in] x One number out of the total sum of the Md5 algorithm
    \param [in] y One number out of the total sum of the Md5 algorithm
    \param [in] z One number out of the total sum of the Md5 algorithm

    \return New number of the total sum of the Md5 algorithm
*/
inline std::uint32_t I(const std::uint32_t& x, const std::uint32_t& y, const std::uint32_t& z) noexcept
{
    return y ^ (x | ~z);
}

/// \brief Convert uint32 to string with hex form of this number
/// \param [in] a uint32 number to convert
/// \return hex represenation of a
std::string Uint32ToHexForm(std::uint32_t a) noexcept
{
    std::string res;
    
    for (int i = 0; i < 4; ++i)
    {
        int lowByte = a % 16;
        a /= 16;
        
        int highByte = a % 16;
        a /= 16;

        if (highByte > 9)
            res += 'a' + highByte - 10;
        else
            res += std::to_string(highByte);

        if (lowByte > 9)
            res += 'a' + lowByte - 10;
        else
            res += std::to_string(lowByte);
    }

    return res;
}

/**
    \brief The function considers the correct padding for the data

    \param [in] data a pointer to the char array to find the padding for
    \param [in] arrayLen the number of elements in the data arr
    \param [in] dataLen the length of the source data

    \return Returns a string with the correct padding of length 64 or 128, depending on the length of the source data
*/
inline std::string DataPadding_MD5(const char* data, const std::size_t& dataLen, const std::size_t& sourceLen) noexcept
{
    // String length in bytes
    std::uint64_t stringLength = sourceLen * 8;
    std::string padding;

    // Set known padding data
    padding.assign(data, dataLen);

    // Add one 1 bit and seven 0 bits to data end. It's equals adding 10000000 or 128 symbol to string end
    padding += static_cast<char>(128);

    // Adding additional bits to make data length equal 512*N + 448, or in chars 64*N + 56
    // Adding eight 0 bits to data end. It's equals adding 00000000 or 0 symbol to string end
    while (padding.length() % 64 != 56)
        padding += '\0';
    
    // String with source string size
    std::vector<char> stringAddition;

    // Pushing symbols to string. Equals 256 based count system
    while (stringLength / 256 > 0)
    {
        stringAddition.emplace_back(static_cast<char>(stringLength % 256));
        stringLength /= 256;
    } 

    // Add last byte to stringAddition
    stringAddition.emplace_back(static_cast<char>(stringLength % 256));
    
    // Adding string addition chars to source string in right order
    // At first we add 4 last bytes(chars). After that we add 4 first bytes(chars).
    // Also this function change bytes position to next function CalculateHastStep_MD5
    for (int i = static_cast<int>(stringAddition.size() - 1); i != -1; --i)
        padding += stringAddition[stringAddition.size() - 1 - i];

    // Add zero bytes to padding    
    for (unsigned int i = 0; i < 8 - stringAddition.size(); ++i)
        padding += '\0'; 

    return padding;
}

/**
    \brief Function for calculating the hashing step

    Calculate hash to 512 bits(64 chars) and change initial numbers

    \param [in] data an array with the source data
    \param [in] dataPos The position from which 64 bytes of the hash should be calculated
    \param [in, out] A0 One number out of the total sum of the Md5 algorithm
    \param [in, out] B0 One number out of the total sum of the Md5 algorithm
    \param [in, out] C0 One number out of the total sum of the Md5 algorithm
    \param [in, out] D0 One number out of the total sum of the Md5 algorithm
*/
void CalculateHashStep_MD5(const char* data, const std::size_t& dataPos, std::uint32_t& A0, std::uint32_t& B0, std::uint32_t& C0, std::uint32_t& D0) noexcept
{
    // Convert every 4 chars to 32 bit int and save it into little endian
    std::uint32_t M[16];
    for (int i = 63; i > -1; i -= 4)
    {
        M[i/4] = 0;
        M[i/4] |= static_cast<unsigned char>(data[dataPos + i]) << 24;
        M[i/4] |= static_cast<unsigned char>(data[dataPos + i - 1]) << 16;
        M[i/4] |= static_cast<unsigned char>(data[dataPos + i - 2]) << 8;
        M[i/4] |= static_cast<unsigned char>(data[dataPos + i - 3]);
    }

    // Save init uints values
    std::uint32_t A = A0;
    std::uint32_t B = B0;
    std::uint32_t C = C0;
    std::uint32_t D = D0;

    for (int i = 0; i < 64; ++i)
    {       
        // New value
        std::uint32_t newVal;
        int g;
        std::uint32_t (*func)(const std::uint32_t&, const std::uint32_t&, const std::uint32_t&) = F;

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

/**
    \brief Md5 hash function

    \param [in] str the string to calculate the hash for
    
    \return hash of a str string in hex form
*/
std::string CalculateHash_MD5(const char* data, const std::size_t& dataLen) noexcept
{
    // A – 01 23 45 67 in little endian order: 67452301
    std::uint32_t A0 = 0x67452301;
    // B - 89 AB CD EF in little endian order: EFCDAB89
    std::uint32_t B0 = 0xefcdab89;
    // C – FE DC BA 98 in little endian order: 98BADCFE
    std::uint32_t C0 = 0x98badcfe;
    // D – 76 54 32 10 in little endian order: 10325476
    std::uint32_t D0 = 0x10325476;

    // Split source string to 512 bits(64 chars) chunks and process all of them
    for (uint64_t i = 0; i < dataLen / 64; ++i)
        CalculateHashStep_MD5(data, i * 64, A0, B0, C0, D0);

    // Padding source string
    std::string padding = DataPadding_MD5(data + (dataLen & ~0b00111111), dataLen & 0b00111111, dataLen);

    CalculateHashStep_MD5(padding.c_str(), 0, A0, B0, C0, D0);

    if (padding.length() > 64)
        CalculateHashStep_MD5(padding.c_str(), 64, A0, B0, C0, D0);

    // Return changed initial uints converted to string with hex form
    return Uint32ToHexForm(A0) + Uint32ToHexForm(B0) + Uint32ToHexForm(C0) + Uint32ToHexForm(D0);
}

std::string CalculateHash_MD5(const std::string& str) noexcept
{
    return CalculateHash_MD5(str.c_str(), str.length());
}

/**
    \brief Md5 hash function for files
    
    File size should be less then 2305843009213693951 bytes or 2097151 TeraBytes

    \param [in] fileName the name of the file to calculate the hash for
    
    \return hash of a fileName file in hex form. Return empty string if failed to open file
*/
std::string CalculateFileHash_MD5(const std::string& fileName) noexcept
{
    // A – 01 23 45 67 in little endian order: 67452301
    std::uint32_t A0 = 0x67452301;
    // B - 89 AB CD EF in little endian order: EFCDAB89
    std::uint32_t B0 = 0xefcdab89;
    // C – FE DC BA 98 in little endian order: 98BADCFE
    std::uint32_t C0 = 0x98badcfe;
    // D – 76 54 32 10 in little endian order: 10325476
    std::uint32_t D0 = 0x10325476;
    
    // Open file
    std::ifstream file(fileName, std::ios_base::binary | std::ios_base::ate);
    if (!file.is_open()) {std::cerr << "Can not open file: " << fileName << std::endl; return "";}

    // Save file size
    uint64_t fileSize = file.tellg();
    file.seekg(0);

    // Arrays to read 4kb from file and to save 4 kb to file
    char fileDataChunk[CHUNK_SIZE];

    // Counter for file reading
    std::size_t counter = 0;

    // Checking whether the file is larger than the size of the file processing chunks
    if (fileSize > CHUNK_SIZE)
    {
        // Processing the part of the file that is a multiple of the chunk size
        for(; counter < fileSize - CHUNK_SIZE; counter += CHUNK_SIZE)
        {
            // Read chunk from input file
            file.read(fileDataChunk, CHUNK_SIZE);

            for (std::size_t i = 0; i < CHUNK_SIZE; i += 64)
                CalculateHashStep_MD5(fileDataChunk, i, A0, B0, C0, D0);
        }
    }

    // Calculating the remaining bytes in the file
    counter = fileSize - counter;

    // Read last bytes from input file
    file.read(fileDataChunk, counter);

    // Calculate hash for last bytes
    for (uint64_t i = 0; i < counter / 64; ++i)
        CalculateHashStep_MD5(fileDataChunk, i * 64, A0, B0, C0, D0);

    // Padding source file
    // Move fileDataChunk ptr to last position multiply by 64
    std::string padding = DataPadding_MD5(fileDataChunk + (counter & ~0b00111111), counter & 0b00111111, fileSize);

    CalculateHashStep_MD5(padding.c_str(), 0, A0, B0, C0, D0);

    if (padding.length() > 64)
        CalculateHashStep_MD5(padding.c_str(), 64, A0, B0, C0, D0);

    // Return changed initial uints converted to string with hex form
    return Uint32ToHexForm(A0) + Uint32ToHexForm(B0) + Uint32ToHexForm(C0) + Uint32ToHexForm(D0);
}

int main()
{
    std::string a = "`1234567890-=qwertyuiop[]asdfghjkl;'zxcvbnm,./~!@#$%^&*()_+QWERTYUIOP{}ASDFGHJKL:|ZXCVBNM<>? And some additional text to more changes and tests";
    std::cout << CalculateHash_MD5(a) << std::endl;

    std::cout <<  CalculateFileHash_MD5("Md5.cpp") << std::endl;
}
