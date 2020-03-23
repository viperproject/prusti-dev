FROM openjdk:buster


RUN apt-get update && apt-get install -y wget && \
    wget -q -O - https://pmserver.inf.ethz.ch/viper/debs/xenial/key.asc | apt-key add - && \
    echo 'deb http://pmserver.inf.ethz.ch/viper/debs/xenial /' | tee /etc/apt/sources.list.d/viper.list && \
    apt-get update && \
    apt-get install -y viper build-essential pkg-config gcc libssl-dev

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/root/.cargo/bin:${PATH}"

COPY . .

RUN make build

